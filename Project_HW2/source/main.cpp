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
//
// Uses a min-heap (priority queue) for O(log n) candidate selection instead
// of O(n) linear scan, significantly improving performance on large inputs.

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <optional>
#include <queue>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace {

template <class T>
using Opt = std::optional<T>;

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
//   (b) detect stale heap entries after a collapse
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
        sum += crossLD(p, q);
    }
    return static_cast<double>(0.5L * sum);
}

// A directed line segment from a to b.
struct Segment {
    Point a;
    Point b;
};

// Returns true if point p lies on segment [a, b] (collinear and within the bbox).
static inline bool onSegment(const Point& a, const Point& b, const Point& p) {
    if (std::abs(static_cast<double>(crossLD(a, b, p))) > 1e-10) {
        return false;
    }
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
static inline bool segmentsIntersectProperOrTouch(const Point& p1, const Point& q1,
                                                   const Point& p2, const Point& q2) {
    const int o1 = orient(p1, q1, p2);
    const int o2 = orient(p1, q1, q2);
    const int o3 = orient(p2, q2, p1);
    const int o4 = orient(p2, q2, q1);

    if (o1 == 0 && onSegment(p1, q1, p2)) return true;
    if (o2 == 0 && onSegment(p1, q1, q2)) return true;
    if (o3 == 0 && onSegment(p2, q2, p1)) return true;
    if (o4 == 0 && onSegment(p2, q2, q1)) return true;

    return (o1 != o2) && (o3 != o4);
}

// Ray-casting point-in-polygon test (strict interior).
static inline bool pointInPolygonStrict(const Point& p, const std::vector<Vertex>& ring) {
    if (ring.size() < 3) return false;

    bool inside = false;
    for (std::size_t i = 0, j = ring.size() - 1; i < ring.size(); j = i++) {
        const Point& a = ring[j].p;
        const Point& b = ring[i].p;

        if (onSegment(a, b, p)) return false;

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
static inline bool ringIsSimple(const std::vector<Vertex>& ring) {
    const auto segs = ringSegments(ring);
    if (segs.size() < 4) return true;

    const std::size_t n = segs.size();
    for (std::size_t i = 0; i < n; ++i) {
        for (std::size_t j = i + 1; j < n; ++j) {
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

// Describes one simplification step.
struct CandidateOp {
    int ring_index{};
    std::size_t remove_index{};
    bool move_prev{};
    Point moved_point{};
    double cost{};
};

// The outer ring must keep at least 4 vertices; holes need only 3.
static inline int ringMinVertices(int ring_id) {
    return (ring_id == 0) ? 4 : 3;
}

// Computes the "move previous" operation for removing vertex C at index idx.
// Finds B' on segment A-B such that removing C and replacing B with B' preserves area.
// Returns (B', displacement_cost) or nullopt if degenerate.
static inline Opt<std::pair<Point, double>>
computeMovePrev(const std::vector<Vertex>& ring, std::size_t idx) {
    const std::size_t n = ring.size();
    const std::size_t iA = (idx + n - 2) % n;
    const std::size_t iB = (idx + n - 1) % n;
    const std::size_t iC = idx;
    const std::size_t iD = (idx + 1) % n;

    const Point A = ring[iA].p;
    const Point B = ring[iB].p;
    const Point C = ring[iC].p;
    const Point D = ring[iD].p;

    const long double crossAB = crossLD(A, B);
    const long double crossBC = crossLD(B, C);
    const long double crossCD = crossLD(C, D);
    const long double K = crossAB + crossBC + crossCD;

    const long double crossAD = crossLD(A, D);
    const long double crossBD = crossLD(B, D);
    const long double denom = crossAB + crossBD - crossAD;

    if (std::abs(static_cast<double>(denom)) < 1e-15) {
        return std::nullopt;
    }

    const long double t = (K - crossAD) / denom;
    if (!std::isfinite(static_cast<double>(t)) || std::abs(static_cast<double>(t)) < 1e-15) {
        return std::nullopt;
    }

    const Point Bp{A.x + static_cast<double>(t) * (B.x - A.x),
                   A.y + static_cast<double>(t) * (B.y - A.y)};

    const double area2  = area2TriangleAbs(B, C, D);
    const double factor = std::abs(1.0 - 1.0 / static_cast<double>(t));
    const double cost   = factor * area2;

    return std::make_pair(Bp, cost);
}

// Computes the "move next" operation for removing vertex C at index idx.
// Finds D' on segment D-E such that removing C and replacing D with D' preserves area.
// Returns (D', displacement_cost) or nullopt if degenerate.
static inline Opt<std::pair<Point, double>>
computeMoveNext(const std::vector<Vertex>& ring, std::size_t idx) {
    const std::size_t n = ring.size();
    const std::size_t iB = (idx + n - 1) % n;
    const std::size_t iC = idx;
    const std::size_t iD = (idx + 1) % n;
    const std::size_t iE = (idx + 2) % n;

    const Point B = ring[iB].p;
    const Point C = ring[iC].p;
    const Point D = ring[iD].p;
    const Point E = ring[iE].p;

    const long double crossBC = crossLD(B, C);
    const long double crossCD = crossLD(C, D);
    const long double crossDE = crossLD(D, E);
    const long double K = crossBC + crossCD + crossDE;

    const long double crossBD = crossLD(B, D);
    const long double crossBE = crossLD(B, E);
    const long double denom   = crossBE - crossBD - crossDE;

    if (std::abs(static_cast<double>(denom)) < 1e-15) {
        return std::nullopt;
    }

    const long double beta = (K - crossBD - crossDE) / denom;
    if (!std::isfinite(static_cast<double>(beta))) {
        return std::nullopt;
    }

    const double oneMinus = 1.0 - static_cast<double>(beta);
    if (std::abs(oneMinus) < 1e-15) {
        return std::nullopt;
    }

    const Point Dp{D.x + static_cast<double>(beta) * (E.x - D.x),
                   D.y + static_cast<double>(beta) * (E.y - D.y)};

    const double area2  = area2TriangleAbs(B, C, D);
    const double factor = std::abs(static_cast<double>(beta) / oneMinus);
    const double cost   = factor * area2;

    return std::make_pair(Dp, cost);
}

// Applies a CandidateOp to one ring and returns the modified ring.
static inline std::vector<Vertex> applyOpToRing(const std::vector<Vertex>& ring,
                                                  const CandidateOp& op) {
    const std::size_t n = ring.size();
    std::vector<Vertex> out;
    out.reserve(n - 1);

    const std::size_t idxRemove = op.remove_index;
    const std::size_t idxMove = op.move_prev ? (idxRemove + n - 1) % n
                                              : (idxRemove + 1)     % n;

    for (std::size_t i = 0; i < n; ++i) {
        if (i == idxRemove) continue;
        Vertex v = ring[i];
        if (i == idxMove) v.p = op.moved_point;
        out.push_back(v);
    }
    return out;
}

// Checks whether applying op leaves all topology invariants satisfied.
static inline bool topologyOkAfterApplying(const std::vector<std::vector<Vertex>>& rings,
                                            const std::vector<int>& /*ringIds*/,
                                            const CandidateOp& op) {
    // Build the candidate ring only once
    std::vector<std::vector<Vertex>> tmp = rings;
    const std::size_t ri = static_cast<std::size_t>(op.ring_index);
    tmp[ri] = applyOpToRing(tmp[ri], op);

    // Fast local self-intersection check: only test the ~4 new segments
    // against all other segments in the same ring
    {
        const auto& ring = tmp[ri];
        const std::size_t n = ring.size();
        if (n >= 4) {
            // Find which indices changed (the moved vertex neighbourhood)
            // Check all pairs involving the moved vertex's new edges
            const auto segs = ringSegments(ring);
            for (std::size_t i = 0; i < n; ++i) {
                for (std::size_t j = i + 2; j < n; ++j) {
                    if (i == 0 && j == n - 1) continue; // adjacent (wrap)
                    if (segmentsIntersectProperOrTouch(segs[i].a, segs[i].b,
                                                       segs[j].a, segs[j].b))
                        return false;
                }
            }
        }
    }

    // Ring-ring disjointness (still needed for multi-ring polygons)
    if (!ringsAreDisjoint(tmp)) return false;

    // Hole containment: check ALL hole vertices, not just [0]
    if (!tmp.empty()) {
        const auto& outer = tmp[0];
        for (std::size_t i = 1; i < tmp.size(); ++i) {
            if (tmp[i].empty()) return false;
            for (const auto& v : tmp[i]) {           // ← all vertices
                if (!pointInPolygonStrict(v.p, outer)) return false;
            }
        }
    }

    return true;
}

// Entry in the priority queue (min-heap by cost).
// Stores enough information to validate whether the entry is still current
// (stale entries arise when a neighbouring vertex is moved after this was enqueued).
struct HeapEntry {
    double      cost{};
    int         ring_index{};
    std::size_t remove_index{};
    int         original_id{};   // original_id of the vertex being removed
    bool        move_prev{};
    Point       moved_point{};

    // min-heap: smallest cost at the top
    bool operator>(const HeapEntry& o) const {
        if (!nearlyEqual(cost, o.cost, 1e-12)) return cost > o.cost;
        if (ring_index != o.ring_index)        return ring_index > o.ring_index;
        return original_id > o.original_id;
    }
};

// Rotates a ring so the vertex with original_id == 0 is first.
static inline std::vector<Vertex> rotateToOriginalZeroIfPresent(std::vector<Vertex> ring) {
    if (ring.empty()) return ring;

    auto it = std::find_if(ring.begin(), ring.end(),
                           [](const Vertex& v) { return v.original_id == 0; });
    if (it == ring.end()) {
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

// Reads a CSV file with header "ring_id,vertex_id,x,y".
static inline bool parseInput(const std::string& path,
                               std::vector<int>& ringIdsOut,
                               std::vector<std::vector<Vertex>>& ringsOut) {
    std::ifstream in(path);
    if (!in) return false;

    std::string line;
    if (!std::getline(in, line)) return false;

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
    if (argc < 3) {
        std::cerr << "Usage: "
                  << (argc > 0 ? argv[0] : "simplify")
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

    // Record input area before simplification
    const double inputArea = [&]() {
        double s = 0.0;
        for (const auto& r : rings) s += signedRingArea(r);
        return s;
    }();

    double totalArealDisplacement = 0.0;

    // -----------------------------------------------------------------------
    // Priority-queue based greedy simplification
    // -----------------------------------------------------------------------
    // Each HeapEntry records the cost of collapsing a specific vertex.
    // After each collapse, only the affected ring's entries are re-enqueued;
    // stale entries (where original_id no longer matches) are discarded lazily.
    // -----------------------------------------------------------------------

    using MinHeap = std::priority_queue<HeapEntry,
                                        std::vector<HeapEntry>,
                                        std::greater<HeapEntry>>;
    MinHeap pq;

    // Enqueue both move-prev and move-next candidates for vertex i in ring ri.
    auto enqueueVertex = [&](int ri, std::size_t i) {
        const auto& ring  = rings[static_cast<std::size_t>(ri)];
        const int ring_id = ringIds[static_cast<std::size_t>(ri)];
        const int minV    = ringMinVertices(ring_id);

        if (static_cast<int>(ring.size()) <= minV) return;
        if (ring[i].original_id == 0) return;
        if (ring.size() - 1 < static_cast<std::size_t>(minV)) return;

        if (const auto mv = computeMovePrev(ring, i)) {
            pq.push(HeapEntry{mv->second, ri, i,
                              ring[i].original_id, true, mv->first});
        }
        if (const auto mv = computeMoveNext(ring, i)) {
            pq.push(HeapEntry{mv->second, ri, i,
                              ring[i].original_id, false, mv->first});
        }
    };

    // Initial population of the heap
    for (int ri = 0; ri < static_cast<int>(rings.size()); ++ri) {
        for (std::size_t i = 0; i < rings[static_cast<std::size_t>(ri)].size(); ++i) {
            enqueueVertex(ri, i);
        }
    }

    // Main greedy loop
    while (totalVertexCount(rings) > target && !pq.empty()) {
        const HeapEntry top = pq.top();
        pq.pop();

        const auto& ring = rings[static_cast<std::size_t>(top.ring_index)];

        // Stale check 1: index out of range after a previous collapse
        if (top.remove_index >= ring.size()) continue;

        // Stale check 2: the vertex at this index is no longer the same one
        if (ring[top.remove_index].original_id != top.original_id) continue;

        // Build a CandidateOp and verify topology
        CandidateOp op;
        op.ring_index   = top.ring_index;
        op.remove_index = top.remove_index;
        op.move_prev    = top.move_prev;
        op.moved_point  = top.moved_point;
        op.cost         = top.cost;

        if (!topologyOkAfterApplying(rings, ringIds, op)) continue;

        // Apply the collapse
        totalArealDisplacement += op.cost;
        rings[static_cast<std::size_t>(op.ring_index)] =
            applyOpToRing(rings[static_cast<std::size_t>(op.ring_index)], op);

        // Re-enqueue all vertices in the affected ring
        // (their neighbourhoods have changed; old entries will be discarded as stale)
        const std::size_t ri = static_cast<std::size_t>(op.ring_index);
        for (std::size_t i = 0; i < rings[ri].size(); ++i) {
            enqueueVertex(op.ring_index, i);
        }
    }

    // Rotate each output ring so it starts at the original vertex 0
    for (auto& r : rings) r = rotateToOriginalZeroIfPresent(std::move(r));

    // Compute output area
    const double outputArea = [&]() {
        double s = 0.0;
        for (const auto& r : rings) s += signedRingArea(r);
        return s;
    }();

    // Warn if area drifted beyond floating-point tolerance
    if (std::abs(outputArea - inputArea) > 1e-6 * std::abs(inputArea)) {
        std::cerr << "WARNING: area drift detected: in=" << inputArea << " out=" << outputArea << "\n";
    }

    // --- Output ---
    std::cout << "ring_id,vertex_id,x,y\n";
    std::cout << std::setprecision(11) << std::defaultfloat;

    for (std::size_t ri = 0; ri < rings.size(); ++ri) {
        const int ring_id  = ringIds[ri];
        const auto& ring   = rings[ri];
        for (std::size_t vi = 0; vi < ring.size(); ++vi) {
            std::cout << ring_id << "," << vi << ","
                      << ring[vi].p.x << "," << ring[vi].p.y << "\n";
        }
    }

    std::cout << std::scientific << std::setprecision(6);
    std::cout << "Total signed area in input: "   << inputArea              << "\n";
    std::cout << "Total signed area in output: "  << outputArea             << "\n";
    std::cout << "Total areal displacement: "     << totalArealDisplacement << "\n";

    return 0;
}