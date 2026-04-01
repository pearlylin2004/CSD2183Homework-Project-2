// Area- and Topology-Preserving Polygon Simplification
//
// Reads polygon rings from a CSV file (ring_id, vertex_id, x, y),
// greedily simplifies them while preserving total signed area and avoiding
// topology changes (self-intersections, ring-ring intersections, and holes
// escaping the outer boundary), then prints the simplified rings plus metrics.
//
// Output format matches the provided test cases:
// - ring_id,vertex_id,x,y lines for each output vertex
// - Total signed area in input / output
// - Total areal displacement (sum of per-operation displacement costs)

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#if (defined(_MSVC_LANG) && _MSVC_LANG >= 201703L) || (__cplusplus >= 201703L)
#include <optional>
#else
#include <experimental/optional>
#endif
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace {

#if (defined(_MSVC_LANG) && _MSVC_LANG >= 201703L) || (__cplusplus >= 201703L)
template <class T>
using Opt = std::optional<T>;
constexpr std::nullopt_t nullopt_v = std::nullopt;
#else
template <class T>
using Opt = std::experimental::optional<T>;
constexpr std::experimental::nullopt_t nullopt_v = std::experimental::nullopt;
#endif

// Small epsilon used for floating-point comparisons and degenerate-case guards.
constexpr double kEps = 1e-12;

// 2D point with double-precision coordinates.
struct Point {
    double x{};
    double y{};
};

// A polygon vertex: stores a 2D position plus its original vertex_id from the CSV.
// original_id is kept so we can:
//   (a) skip the anchor vertex (id == 0) during simplification
//   (b) deterministically break cost ties (prefer lower ring_id then lower vertex_id)
//   (c) rotate the output ring so it still starts at the original vertex 0
struct Vertex {
    Point p;
    int original_id{};
};

// Returns true if |a - b| <= eps.
static inline bool nearlyEqual(double a, double b, double eps = kEps) {
    return std::abs(a - b) <= eps;
}

// 2D cross product a.x*b.y - a.y*b.x, computed in long double for stability.
static inline long double crossLD(const Point& a, const Point& b) {
    return static_cast<long double>(a.x) * static_cast<long double>(b.y)
         - static_cast<long double>(a.y) * static_cast<long double>(b.x);
}

// Cross product of vectors (b-a) and (c-a), i.e. the signed area of triangle abc x2.
static inline long double crossLD(const Point& a, const Point& b, const Point& c) {
    return crossLD(Point{b.x - a.x, b.y - a.y}, Point{c.x - a.x, c.y - a.y});
}

// Returns |(b-a) x (c-a)|  -- twice the unsigned area of triangle abc.
static inline double area2TriangleAbs(const Point& a, const Point& b, const Point& c) {
    const long double v = crossLD(a, b, c);
    return static_cast<double>(std::abs(v));
}

// Shoelace (surveyor's) formula: signed area of a closed polygon ring.
// Positive means counter-clockwise winding; negative means clockwise.
static inline double signedRingArea(const std::vector<Vertex>& ring) {
    if (ring.size() < 3) {
        return 0.0;
    }
    long double sum = 0.0L;
    for (std::size_t i = 0; i < ring.size(); ++i) {
        const auto& p = ring[i].p;
        const auto& q = ring[(i + 1) % ring.size()].p;
        sum += crossLD(p, q);  // accumulates cross products p x q
    }
    return static_cast<double>(0.5L * sum);
}

// A directed line segment from a to b.
struct Segment {
    Point a;
    Point b;
};

// Returns true if point p lies on segment [a, b] (collinear and within the bbox).
// Uses a 1e-10 tolerance so near-collinear points are treated as on the segment.
static inline bool onSegment(const Point& a, const Point& b, const Point& p) {
    if (std::abs(static_cast<double>(crossLD(a, b, p))) > 1e-10) {
        return false;  // not collinear
    }
    // Check bounding-box containment with a small tolerance
    return (std::min(a.x, b.x) - 1e-10 <= p.x && p.x <= std::max(a.x, b.x) + 1e-10) &&
           (std::min(a.y, b.y) - 1e-10 <= p.y && p.y <= std::max(a.y, b.y) + 1e-10);
}

// Returns the orientation of triangle (a, b, c):
//  +1 = counter-clockwise, -1 = clockwise, 0 = collinear.
static inline int orient(const Point& a, const Point& b, const Point& c) {
    const long double v = crossLD(a, b, c);
    if (v >  1e-12L) return  1;
    if (v < -1e-12L) return -1;
    return 0;
}

// Returns true if segments (p1,q1) and (p2,q2) share any point,
// including endpoints and collinear overlaps.
// Uses the standard orientation-based intersection test.
static inline bool segmentsIntersectProperOrTouch(const Point& p1, const Point& q1,
                                                   const Point& p2, const Point& q2) {
    const int o1 = orient(p1, q1, p2);
    const int o2 = orient(p1, q1, q2);
    const int o3 = orient(p2, q2, p1);
    const int o4 = orient(p2, q2, q1);

    // Collinear endpoint cases: check if the endpoint lies on the other segment
    if (o1 == 0 && onSegment(p1, q1, p2)) return true;
    if (o2 == 0 && onSegment(p1, q1, q2)) return true;
    if (o3 == 0 && onSegment(p2, q2, p1)) return true;
    if (o4 == 0 && onSegment(p2, q2, q1)) return true;

    // General proper intersection: the two endpoints of each segment straddle the other
    return (o1 != o2) && (o3 != o4);
}

// Ray-casting point-in-polygon test (strict interior).
// Returns false if p lies exactly on the boundary.
static inline bool pointInPolygonStrict(const Point& p, const std::vector<Vertex>& ring) {
    if (ring.size() < 3) return false;

    bool inside = false;
    for (std::size_t i = 0, j = ring.size() - 1; i < ring.size(); j = i++) {
        const Point& a = ring[j].p;
        const Point& b = ring[i].p;

        // If p is exactly on this edge, it is not strictly interior
        if (onSegment(a, b, p)) return false;

        // Standard ray-cast crossing test (horizontal ray from p rightward)
        const bool intersect = ((a.y > p.y) != (b.y > p.y)) &&
                               (p.x < (b.x - a.x) * (p.y - a.y) / (b.y - a.y + 0.0) + a.x);
        if (intersect) inside = !inside;
    }
    return inside;
}

// Builds the list of directed edge segments for a ring.
static inline std::vector<Segment> ringSegments(const std::vector<Vertex>& ring) {
    std::vector<Segment> segs;
    if (ring.size() < 2) return segs;
    segs.reserve(ring.size());
    for (std::size_t i = 0; i < ring.size(); ++i) {
        segs.push_back(Segment{ring[i].p, ring[(i + 1) % ring.size()].p});
    }
    return segs;
}

// Returns true if the ring has no self-intersections (i.e. is a simple polygon).
// Adjacent edges share an endpoint by construction, so they are skipped.
// A triangle (3 edges) cannot self-intersect, so we short-circuit for size < 4.
static inline bool ringIsSimple(const std::vector<Vertex>& ring) {
    const auto segs = ringSegments(ring);
    if (segs.size() < 4) return true;  // triangles are always simple

    const std::size_t n = segs.size();
    for (std::size_t i = 0; i < n; ++i) {
        for (std::size_t j = i + 1; j < n; ++j) {
            // Skip edge pairs that share a vertex (they are adjacent)
            const bool adjacent = (j == i) || (j == (i + 1) % n) || (i == (j + 1) % n);
            if (adjacent) continue;
            if (segmentsIntersectProperOrTouch(segs[i].a, segs[i].b,
                                               segs[j].a, segs[j].b)) {
                return false;
            }
        }
    }
    return true;
}

// Returns true if no two rings in the collection share any boundary point or overlap.
static inline bool ringsAreDisjoint(const std::vector<std::vector<Vertex>>& rings) {
    // Pre-build all segment lists to avoid recomputing in the inner loop
    std::vector<std::vector<Segment>> allSegs;
    allSegs.reserve(rings.size());
    for (const auto& r : rings) allSegs.push_back(ringSegments(r));

    for (std::size_t i = 0; i < rings.size(); ++i) {
        for (std::size_t j = i + 1; j < rings.size(); ++j) {
            for (const auto& s1 : allSegs[i]) {
                for (const auto& s2 : allSegs[j]) {
                    if (segmentsIntersectProperOrTouch(s1.a, s1.b, s2.a, s2.b))
                        return false;
                }
            }
        }
    }
    return true;
}

// Returns the total number of vertices across all rings.
static inline std::size_t totalVertexCount(const std::vector<std::vector<Vertex>>& rings) {
    std::size_t c = 0;
    for (const auto& r : rings) c += r.size();
    return c;
}

// Describes one simplification step:
//   - Remove the vertex at remove_index in rings[ring_index]
//   - Move either the previous vertex (move_prev=true) or next vertex (move_prev=false)
//     to moved_point so that the signed area is preserved exactly
//   - cost is the areal displacement incurred by this move
struct CandidateOp {
    int ring_index{};
    std::size_t remove_index{};
    bool move_prev{};       // true = slide the predecessor; false = slide the successor
    Point moved_point{};
    double cost{};          // areal displacement = |triangle area| * scale factor
};

// The outer ring (ring_id == 0) must keep at least 4 vertices (a valid polygon
// with distinct corners), while hole rings only need 3 (a triangle is the minimum).
static inline int ringMinVertices(int ring_id) {
    return (ring_id == 0) ? 4 : 3;
}

// Computes the "move previous" operation for removing vertex C at index idx.
//
// Neighbourhood: A - B - C - D  (indices iA, iB=idx-1, iC=idx, iD=idx+1)
//
// We want to find a new position B' on segment A-B such that removing C and
// replacing B with B' leaves the signed ring area unchanged.
//
// Derivation:
//   The shoelace area contribution of the four consecutive cross-products
//   crossLD(A,B) + crossLD(B,C) + crossLD(C,D)  changes when we:
//     - replace B with B' = A + t*(B-A)
//     - remove C
//   Setting the new contribution equal to K = original contribution gives a
//   linear equation in t, solved below.
//
// Returns (B', displacement_cost) or nullopt if the problem is degenerate.
static inline Opt<std::pair<Point, double>>
computeMovePrev(const std::vector<Vertex>& ring, std::size_t idx) {
    const std::size_t n = ring.size();
    const std::size_t iA = (idx + n - 2) % n;
    const std::size_t iB = (idx + n - 1) % n;  // vertex to be moved
    const std::size_t iC = idx;                  // vertex to be removed
    const std::size_t iD = (idx + 1) % n;

    const Point A = ring[iA].p;
    const Point B = ring[iB].p;
    const Point C = ring[iC].p;
    const Point D = ring[iD].p;

    // Sum of the three cross-products we are replacing (= K, the invariant)
    const long double crossAB = crossLD(A, B);
    const long double crossBC = crossLD(B, C);
    const long double crossCD = crossLD(C, D);
    const long double K = crossAB + crossBC + crossCD;

    // After the operation: cross(A, B') + cross(B', D) must equal K
    // B' = A + t*(B-A), so:
    //   cross(A, A+t*(B-A)) + cross(A+t*(B-A), D) = K
    // Expanding and collecting terms in t gives:
    //   t * (cross(A,B) + cross(B,D) - cross(A,D))  =  K - cross(A,D)
    const long double crossAD = crossLD(A, D);
    const long double crossBD = crossLD(B, D);
    const long double denom = crossAB + crossBD - crossAD;

    if (std::abs(static_cast<double>(denom)) < 1e-15) {
        return nullopt_v;  // degenerate: A, B, D are collinear
    }

    const long double t = (K - crossAD) / denom;
    if (!std::isfinite(static_cast<double>(t)) || std::abs(static_cast<double>(t)) < 1e-15) {
        return nullopt_v;  // t=0 would collapse B' onto A
    }

    // New position of B: interpolate along A->B using parameter t
    const Point Bp{A.x + static_cast<double>(t) * (B.x - A.x),
                   A.y + static_cast<double>(t) * (B.y - A.y)};

    // Areal displacement = |triangle BCD| * |1 - 1/t|
    // This quantifies how much area the triangle sweeps as B moves to B'
    const double area2  = area2TriangleAbs(B, C, D);
    const double factor = std::abs(1.0 - 1.0 / static_cast<double>(t));
    const double cost   = factor * area2;

    return std::make_pair(Bp, cost);
}

// Computes the "move next" operation for removing vertex C at index idx.
//
// Neighbourhood: B - C - D - E  (indices iB=idx-1, iC=idx, iD=idx+1, iE=idx+2)
//
// Analogous to computeMovePrev but the successor D is moved to D' = D + beta*(E-D).
// The same area-preservation constraint gives a linear equation in beta.
//
// Returns (D', displacement_cost) or nullopt if degenerate.
static inline Opt<std::pair<Point, double>>
computeMoveNext(const std::vector<Vertex>& ring, std::size_t idx) {
    const std::size_t n = ring.size();
    const std::size_t iB = (idx + n - 1) % n;
    const std::size_t iC = idx;                  // vertex to be removed
    const std::size_t iD = (idx + 1) % n;        // vertex to be moved
    const std::size_t iE = (idx + 2) % n;

    const Point B = ring[iB].p;
    const Point C = ring[iC].p;
    const Point D = ring[iD].p;
    const Point E = ring[iE].p;

    // Invariant K: sum of the three cross-products being replaced
    const long double crossBC = crossLD(B, C);
    const long double crossCD = crossLD(C, D);
    const long double crossDE = crossLD(D, E);
    const long double K = crossBC + crossCD + crossDE;

    // After removing C and moving D to D' = D + beta*(E-D):
    //   cross(B, D') + cross(D', E) = K
    // Expanding gives a linear equation in beta:
    //   beta * (cross(B,E) - cross(B,D) - cross(D,E)) = K - cross(B,D) - cross(D,E)
    const long double crossBD = crossLD(B, D);
    const long double crossBE = crossLD(B, E);
    const long double denom   = crossBE - crossBD - crossDE;

    if (std::abs(static_cast<double>(denom)) < 1e-15) {
        return nullopt_v;  // degenerate
    }

    const long double beta = (K - crossBD - crossDE) / denom;
    if (!std::isfinite(static_cast<double>(beta))) {
        return nullopt_v;
    }

    const double oneMinus = 1.0 - static_cast<double>(beta);
    if (std::abs(oneMinus) < 1e-15) {
        return nullopt_v;  // D' would land exactly on E
    }

    // New position of D: interpolate along D->E by beta
    const Point Dp{D.x + static_cast<double>(beta) * (E.x - D.x),
                   D.y + static_cast<double>(beta) * (E.y - D.y)};

    // Areal displacement = |triangle BCD| * |beta / (1 - beta)|
    const double area2  = area2TriangleAbs(B, C, D);
    const double factor = std::abs(static_cast<double>(beta) / oneMinus);
    const double cost   = factor * area2;

    return std::make_pair(Dp, cost);
}

// Applies a CandidateOp to one ring and returns the modified ring.
// The vertex at remove_index is dropped; the vertex at idxMove is updated
// to op.moved_point so area is preserved.
static inline std::vector<Vertex> applyOpToRing(const std::vector<Vertex>& ring,
                                                  const CandidateOp& op) {
    const std::size_t n = ring.size();
    std::vector<Vertex> out;
    out.reserve(n - 1);  // result has exactly one fewer vertex

    const std::size_t idxRemove = op.remove_index;
    // Predecessor if move_prev, successor otherwise
    const std::size_t idxMove = op.move_prev ? (idxRemove + n - 1) % n
                                              : (idxRemove + 1)     % n;

    for (std::size_t i = 0; i < n; ++i) {
        if (i == idxRemove) continue;  // skip the removed vertex
        Vertex v = ring[i];
        if (i == idxMove) v.p = op.moved_point;  // update the moved vertex
        out.push_back(v);
    }
    return out;
}

// Checks whether applying op leaves all topology invariants satisfied:
//   1. Every ring remains a simple polygon (no self-intersections).
//   2. No two rings share a boundary point or overlap (rings are disjoint).
//   3. Every hole ring (index > 0) has at least one vertex strictly inside the outer ring.
static inline bool topologyOkAfterApplying(const std::vector<std::vector<Vertex>>& rings,
                                            const std::vector<int>& ringIds,
                                            const CandidateOp& op) {
    // Apply the operation to a temporary copy
    std::vector<std::vector<Vertex>> tmp = rings;
    tmp[static_cast<std::size_t>(op.ring_index)] =
        applyOpToRing(tmp[static_cast<std::size_t>(op.ring_index)], op);

    // Check 1: all rings must still be simple
    for (const auto& r : tmp) {
        if (!ringIsSimple(r)) return false;
    }

    // Check 2: no two rings may share any boundary point
    if (!ringsAreDisjoint(tmp)) return false;

    // Check 3: every hole must still be contained within the outer ring
    if (!tmp.empty()) {
        const auto& outer = tmp[0];
        for (std::size_t i = 1; i < tmp.size(); ++i) {
            if (tmp[i].empty()) return false;
            if (!pointInPolygonStrict(tmp[i][0].p, outer)) return false;
        }
    }

    return true;
}

// Greedy best-operation search: scans every non-anchor vertex of every ring,
// tries both move-prev and move-next, and returns the operation with the
// lowest areal displacement cost that also passes all topology checks.
//
// Tie-breaking is deterministic: prefer lower ring_id, then lower original_id.
// Returns nullopt if no valid operation exists or we are already at the target.
static inline Opt<CandidateOp>
findBestOp(const std::vector<std::vector<Vertex>>& rings,
           const std::vector<int>& ringIds,
           std::size_t target) {
    if (totalVertexCount(rings) <= target) return nullopt_v;

    Opt<CandidateOp> best;

    for (std::size_t r = 0; r < rings.size(); ++r) {
        const int ring_id = ringIds[r];
        const auto& ring  = rings[r];
        const int minV    = ringMinVertices(ring_id);

        // Skip rings that are already at their minimum vertex count
        if (static_cast<int>(ring.size()) <= minV) continue;

        for (std::size_t i = 0; i < ring.size(); ++i) {
            // Skip the anchor vertex (original_id == 0) to keep the ring's
            // starting reference stable across iterations
            if (ring[i].original_id == 0) continue;

            // Guard: after removal this ring must still have >= minV vertices
            if (ring.size() - 1 < static_cast<std::size_t>(minV)) continue;

            // --- Try move-prev operation ---
            if (const auto mv = computeMovePrev(ring, i)) {
                CandidateOp op;
                op.ring_index   = static_cast<int>(r);
                op.remove_index = i;
                op.move_prev    = true;
                op.moved_point  = mv->first;
                op.cost         = mv->second;

                if (topologyOkAfterApplying(rings, ringIds, op)) {
                    // Accept if strictly cheaper, or equal cost with lower id
                    if (!best || op.cost < best->cost - 1e-12 ||
                        (nearlyEqual(op.cost, best->cost, 1e-12) &&
                         (ring_id < ringIds[best->ring_index] ||
                          (ring_id == ringIds[best->ring_index] &&
                           ring[i].original_id < rings[best->ring_index][best->remove_index].original_id)))) {
                        best = op;
                    }
                }
            }

            // --- Try move-next operation ---
            if (const auto mv = computeMoveNext(ring, i)) {
                CandidateOp op;
                op.ring_index   = static_cast<int>(r);
                op.remove_index = i;
                op.move_prev    = false;
                op.moved_point  = mv->first;
                op.cost         = mv->second;

                if (topologyOkAfterApplying(rings, ringIds, op)) {
                    if (!best || op.cost < best->cost - 1e-12 ||
                        (nearlyEqual(op.cost, best->cost, 1e-12) &&
                         (ring_id < ringIds[best->ring_index] ||
                          (ring_id == ringIds[best->ring_index] &&
                           ring[i].original_id < rings[best->ring_index][best->remove_index].original_id)))) {
                        best = op;
                    }
                }
            }
        }
    }

    return best;
}

// Rotates a ring so the vertex with original_id == 0 is first.
// If original_id 0 was removed, falls back to the vertex with the smallest original_id.
// This keeps the output vertex ordering stable and matching expected test output.
static inline std::vector<Vertex> rotateToOriginalZeroIfPresent(std::vector<Vertex> ring) {
    if (ring.empty()) return ring;

    auto it = std::find_if(ring.begin(), ring.end(),
                           [](const Vertex& v) { return v.original_id == 0; });
    if (it == ring.end()) {
        // Fallback: start at the smallest surviving original_id
        auto it2 = std::min_element(ring.begin(), ring.end(),
                                    [](const Vertex& a, const Vertex& b) {
                                        return a.original_id < b.original_id;
                                    });
        std::rotate(ring.begin(), it2, ring.end());
        return ring;
    }

    std::rotate(ring.begin(), it, ring.end());
    return ring;
}

// Splits a comma-separated line into tokens.
static inline std::vector<std::string> splitCsvLine(const std::string& line) {
    std::vector<std::string> parts;
    std::stringstream ss(line);
    std::string item;
    while (std::getline(ss, item, ',')) parts.push_back(item);
    return parts;
}

// Reads a CSV file with header "ring_id,vertex_id,x,y" and populates
// ringIdsOut (in ascending ring_id order, outer ring first) and ringsOut.
// Returns false if the file cannot be opened.
static inline bool parseInput(const std::string& path,
                               std::vector<int>& ringIdsOut,
                               std::vector<std::vector<Vertex>>& ringsOut) {
    std::ifstream in(path);
    if (!in) return false;

    std::string line;
    if (!std::getline(in, line)) return false;  // consume header row

    // Use a nested map to collect vertices grouped by ring_id then vertex_id
    // (std::map keeps them sorted, so vertices will be in correct order)
    std::map<int, std::map<int, Point>> byRing;

    while (std::getline(in, line)) {
        if (line.empty()) continue;
        const auto parts = splitCsvLine(line);
        if (parts.size() < 4) continue;

        const int    ring_id   = std::stoi(parts[0]);
        const int    vertex_id = std::stoi(parts[1]);
        const double x         = std::stod(parts[2]);
        const double y         = std::stod(parts[3]);
        byRing[ring_id][vertex_id] = Point{x, y};
    }

    ringIdsOut.clear();
    ringsOut.clear();
    ringIdsOut.reserve(byRing.size());
    ringsOut.reserve(byRing.size());

    for (auto& [rid, verts] : byRing) {
        ringIdsOut.push_back(rid);
        std::vector<Vertex> ring;
        ring.reserve(verts.size());
        for (auto& [vid, p] : verts) ring.push_back(Vertex{p, vid});
        ringsOut.push_back(std::move(ring));
    }

    // Ensure the outer ring (ring_id == 0) is always at index 0
    if (!ringsOut.empty() && ringIdsOut[0] != 0) {
        auto it = std::find(ringIdsOut.begin(), ringIdsOut.end(), 0);
        if (it != ringIdsOut.end()) {
            const std::size_t idx = static_cast<std::size_t>(
                std::distance(ringIdsOut.begin(), it));
            std::swap(ringIdsOut[0], ringIdsOut[idx]);
            std::swap(ringsOut[0],   ringsOut[idx]);
        }
    }

    return true;
}

}  // namespace

int main(int argc, char** argv) {
    // Require exactly: <program> <input_csv> <target_vertex_count>
    if (argc < 3) {
        std::cerr << "Usage: "
                  << (argc > 0 ? argv[0] : "area_and_topology_preserving_polygon_simplification")
                  << " <input_file> <target_vertices>\n";
        return 1;
    }

    const std::string inputPath = argv[1];
    const std::size_t target    = static_cast<std::size_t>(std::stoll(argv[2]));

    std::vector<int> ringIds;
    std::vector<std::vector<Vertex>> rings;
    if (!parseInput(inputPath, ringIds, rings)) {
        std::cerr << "Failed to read input file: " << inputPath << "\n";
        return 1;
    }

    // Record the input area before any simplification for the metrics output
    const double inputArea = [&]() {
        double s = 0.0;
        for (const auto& r : rings) s += signedRingArea(r);
        return s;
    }();

    double totalArealDisplacement = 0.0;

    // Greedy simplification loop: each iteration removes one vertex
    // (the cheapest valid operation) until we reach the target count.
    while (totalVertexCount(rings) > target) {
        const auto best = findBestOp(rings, ringIds, target);
        if (!best) break;  // no valid operation found; stop early

        totalArealDisplacement += best->cost;
        rings[static_cast<std::size_t>(best->ring_index)] =
            applyOpToRing(rings[static_cast<std::size_t>(best->ring_index)], *best);
    }

    // Rotate each output ring so it starts at the original vertex 0 (or lowest id)
    for (auto& r : rings) r = rotateToOriginalZeroIfPresent(std::move(r));

    // Compute output area (should match input area if all operations preserved it)
    const double outputArea = [&]() {
        double s = 0.0;
        for (const auto& r : rings) s += signedRingArea(r);
        return s;
    }();

    // --- Output ---
    std::cout << "ring_id,vertex_id,x,y\n";
    std::cout << std::setprecision(11) << std::defaultfloat;

    // Print each vertex with a renumbered vertex_id starting from 0 per ring
    for (std::size_t ri = 0; ri < rings.size(); ++ri) {
        const int ring_id  = ringIds[ri];
        const auto& ring   = rings[ri];
        for (std::size_t vi = 0; vi < ring.size(); ++vi) {
            std::cout << ring_id << "," << vi << ","
                      << ring[vi].p.x << "," << ring[vi].p.y << "\n";
        }
    }

    // Print summary metrics in scientific notation with 6 decimal places
    std::cout << std::scientific << std::setprecision(6);
    std::cout << "Total signed area in input: "   << inputArea              << "\n";
    std::cout << "Total signed area in output: "  << outputArea             << "\n";
    std::cout << "Total areal displacement: "     << totalArealDisplacement << "\n";

    return 0;
}
