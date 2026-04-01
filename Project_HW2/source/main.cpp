// Area- and Topology-Preserving Polygon Simplification
//
// Implements the Area-Preserving Segment Collapse (APSC) algorithm from
// Kronenfeld et al. (2020). Reads polygon rings from a CSV file
// (ring_id, vertex_id, x, y), greedily simplifies them while preserving
// total signed area and avoiding topology changes (self-intersections,
// ring-ring intersections, holes escaping the outer boundary), then
// prints the simplified rings plus metrics.
//
// KEY IMPROVEMENT over the naive O(n^2) version:
//   - A min-heap (priority queue) keeps all candidate operations sorted by
//     cost so we always pop the cheapest one in O(log n).
//   - Lazy deletion: when a vertex is modified or removed its "generation"
//     counter increments; stale heap entries are silently discarded when
//     they do not match the current generation.
//   - After each collapse only the ~4 affected neighbours are re-evaluated
//     rather than rescanning all vertices (local update).
//   - Topology checks are localised: only the two new edges AE and ED are
//     tested against the ring's other segments (and against other rings)
//     instead of re-validating the entire polygon from scratch.
//
// Overall complexity: O(n log n) for n collapses on a ring with no holes.
//
// Output format:
//   ring_id,vertex_id,x,y   (one line per simplified vertex)
//   Total signed area in input:  <scientific>
//   Total signed area in output: <scientific>
//   Total areal displacement:    <scientific>

#include <algorithm>
#include <cassert>
#include <chrono>
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

// -------------------------------------------------------------------------
// Numeric constants
// -------------------------------------------------------------------------

// Primary epsilon for floating-point equality comparisons.
constexpr double kEps = 1e-12;

// -------------------------------------------------------------------------
// Basic geometry types
// -------------------------------------------------------------------------

// 2D point with double-precision coordinates.
struct Point {
    double x{};
    double y{};
};

// A polygon vertex: 2D position plus its original vertex_id from the CSV.
// We keep original_id to:
//   (a) skip the anchor vertex (id == 0) during simplification so the ring
//       can always be rotated back to start at the original first vertex.
//   (b) break cost ties deterministically (lower ring_id wins, then lower
//       original_id within the same ring).
//   (c) rotate the output ring to start at original vertex 0 if it survived.
struct Vertex {
    Point p{};
    int   original_id{};
};

// A directed line segment a -> b.
struct Segment {
    Point a{};
    Point b{};
};

// -------------------------------------------------------------------------
// Low-level geometry helpers
// -------------------------------------------------------------------------

// Floating-point equality within eps.
static inline bool nearlyEqual(double a, double b, double eps = kEps) {
    return std::abs(a - b) <= eps;
}

// 2D cross product  a x b = a.x*b.y - a.y*b.x  in long double for stability.
static inline long double crossLD(const Point& a, const Point& b) {
    return static_cast<long double>(a.x) * static_cast<long double>(b.y)
         - static_cast<long double>(a.y) * static_cast<long double>(b.x);
}

// Cross product of (b-a) and (c-a): twice the signed area of triangle abc.
static inline long double crossLD(const Point& a, const Point& b, const Point& c) {
    return crossLD(Point{b.x - a.x, b.y - a.y}, Point{c.x - a.x, c.y - a.y});
}

// Twice the unsigned area of triangle abc: |(b-a) x (c-a)|.
static inline double area2TriangleAbs(const Point& a, const Point& b, const Point& c) {
    return static_cast<double>(std::abs(crossLD(a, b, c)));
}

// Shoelace formula: signed area of a closed polygon ring.
// Positive = CCW winding (exterior ring); negative = CW (hole).
static inline double signedRingArea(const std::vector<Vertex>& ring) {
    if (ring.size() < 3) return 0.0;
    long double sum = 0.0L;
    const std::size_t n = ring.size();
    for (std::size_t i = 0; i < n; ++i) {
        sum += crossLD(ring[i].p, ring[(i + 1) % n].p);
    }
    return static_cast<double>(0.5L * sum);
}

// Returns true if p lies on segment [a, b] (collinear + inside bbox).
// Tolerance 1e-10 handles near-degenerate cases.
static inline bool onSegment(const Point& a, const Point& b, const Point& p) {
    if (std::abs(static_cast<double>(crossLD(a, b, p))) > 1e-10) return false;
    return (std::min(a.x, b.x) - 1e-10 <= p.x && p.x <= std::max(a.x, b.x) + 1e-10) &&
           (std::min(a.y, b.y) - 1e-10 <= p.y && p.y <= std::max(a.y, b.y) + 1e-10);
}

// Orientation of triangle (a,b,c): +1 CCW, -1 CW, 0 collinear.
static inline int orient(const Point& a, const Point& b, const Point& c) {
    const long double v = crossLD(a, b, c);
    if (v >  1e-12L) return  1;
    if (v < -1e-12L) return -1;
    return 0;
}

// Returns true if segments (p1,q1) and (p2,q2) share any point
// (proper crossing, T-intersection, or collinear overlap).
static inline bool segmentsIntersect(const Point& p1, const Point& q1,
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

// Ray-casting point-in-polygon (strict interior: boundary returns false).
static inline bool pointInPolygonStrict(const Point& p, const std::vector<Vertex>& ring) {
    if (ring.size() < 3) return false;
    bool inside = false;
    for (std::size_t i = 0, j = ring.size() - 1; i < ring.size(); j = i++) {
        const Point& a = ring[j].p;
        const Point& b = ring[i].p;
        if (onSegment(a, b, p)) return false;
        if (((a.y > p.y) != (b.y > p.y)) &&
            (p.x < (b.x - a.x) * (p.y - a.y) / (b.y - a.y) + a.x))
            inside = !inside;
    }
    return inside;
}

// Total vertex count across all rings.
static inline std::size_t totalVertexCount(const std::vector<std::vector<Vertex>>& rings) {
    std::size_t c = 0;
    for (const auto& r : rings) c += r.size();
    return c;
}

// Minimum vertices a ring must keep (outer ring needs 4 to stay a valid quad;
// holes only need 3 — a triangle is the minimal simple polygon).
static inline int ringMinVertices(int ring_id) {
    return (ring_id == 0) ? 4 : 3;
}

// -------------------------------------------------------------------------
// Doubly-linked ring representation
// -------------------------------------------------------------------------
// Each ring is stored as a circular doubly-linked list of nodes so that
// prev/next navigation and vertex removal are O(1) without shifting arrays.

struct RingNode {
    Point p{};
    int   original_id{};
    int   generation{0};  // incremented when this node is moved or removed
    std::size_t prev{};   // index of predecessor in the nodes array
    std::size_t next{};   // index of successor in the nodes array
    bool  alive{true};    // false once the node has been collapsed away
};

// A ring stored as a pool of RingNode objects with circular prev/next links.
// head is the index of an alive node that we treat as the "start" for output.
struct Ring {
    std::vector<RingNode> nodes;  // node pool; indices are stable
    std::size_t           head{}; // index of the first alive node
    std::size_t           size{}; // number of alive nodes
    int                   ring_id{};
};

// Build a Ring from a flat vector<Vertex>.
static Ring buildRing(const std::vector<Vertex>& verts, int ring_id) {
    Ring r;
    r.ring_id = ring_id;
    r.size    = verts.size();
    r.nodes.resize(verts.size());
    for (std::size_t i = 0; i < verts.size(); ++i) {
        r.nodes[i].p           = verts[i].p;
        r.nodes[i].original_id = verts[i].original_id;
        r.nodes[i].prev        = (i + verts.size() - 1) % verts.size();
        r.nodes[i].next        = (i + 1) % verts.size();
        r.nodes[i].alive       = true;
        r.nodes[i].generation  = 0;
    }
    r.head = 0;
    return r;
}

// Flatten a Ring back to a vector<Vertex> starting from head,
// then rotate so original_id==0 comes first (or smallest surviving id).
static std::vector<Vertex> flattenRing(const Ring& ring) {
    std::vector<Vertex> out;
    out.reserve(ring.size);
    std::size_t cur = ring.head;
    for (std::size_t i = 0; i < ring.size; ++i) {
        out.push_back(Vertex{ring.nodes[cur].p, ring.nodes[cur].original_id});
        cur = ring.nodes[cur].next;
    }

    // Rotate so original_id==0 is first (if it survived), else smallest id.
    auto it = std::find_if(out.begin(), out.end(),
                           [](const Vertex& v){ return v.original_id == 0; });
    if (it == out.end()) {
        it = std::min_element(out.begin(), out.end(),
                              [](const Vertex& a, const Vertex& b){
                                  return a.original_id < b.original_id; });
    }
    std::rotate(out.begin(), it, out.end());
    return out;
}

// -------------------------------------------------------------------------
// Area-preserving placement (Kronenfeld et al. 2020)
// -------------------------------------------------------------------------
// Given a 4-vertex window A-B-C-D in the ring, find the position of the new
// Steiner point (either B' on segment A-B, or D' on segment D-E) that:
//   1. Preserves the signed ring area exactly.
//   2. Minimises the resulting areal displacement.
//
// computeMovePrev: remove C, slide B -> B' on ray A->B.
// computeMoveNext: remove C, slide D -> D' on ray D->E.
//
// Both return (new_point, displacement_cost) or nullopt if degenerate.

static inline std::optional<std::pair<Point, double>>
computeMovePrev(const Point& A, const Point& B, const Point& C, const Point& D) {
    // Invariant K = cross(A,B) + cross(B,C) + cross(C,D)
    const long double crossAB = crossLD(A, B);
    const long double crossBC = crossLD(B, C);
    const long double crossCD = crossLD(C, D);
    const long double K       = crossAB + crossBC + crossCD;

    // After replacing B with B'=A+t*(B-A) and removing C:
    //   cross(A,B') + cross(B',D) = K
    // Expanding: t*(crossAB + crossBD - crossAD) = K - crossAD
    const long double crossAD = crossLD(A, D);
    const long double crossBD = crossLD(B, D);
    const long double denom   = crossAB + crossBD - crossAD;

    if (std::abs(static_cast<double>(denom)) < 1e-15) return std::nullopt;

    const long double t = (K - crossAD) / denom;
    if (!std::isfinite(static_cast<double>(t)) ||
        std::abs(static_cast<double>(t)) < 1e-15)
        return std::nullopt;

    const Point Bp{ A.x + static_cast<double>(t) * (B.x - A.x),
                    A.y + static_cast<double>(t) * (B.y - A.y) };

    // Displacement cost = |triangle BCD| * |1 - 1/t|
    const double cost = area2TriangleAbs(B, C, D) *
                        std::abs(1.0 - 1.0 / static_cast<double>(t));
    return std::make_pair(Bp, cost);
}

static inline std::optional<std::pair<Point, double>>
computeMoveNext(const Point& B, const Point& C, const Point& D, const Point& E) {
    // Invariant K = cross(B,C) + cross(C,D) + cross(D,E)
    const long double crossBC = crossLD(B, C);
    const long double crossCD = crossLD(C, D);
    const long double crossDE = crossLD(D, E);
    const long double K       = crossBC + crossCD + crossDE;

    // After removing C and moving D to D'=D+beta*(E-D):
    //   cross(B,D') + cross(D',E) = K
    // Expanding: beta*(crossBE - crossBD - crossDE) = K - crossBD - crossDE
    const long double crossBD = crossLD(B, D);
    const long double crossBE = crossLD(B, E);
    const long double denom   = crossBE - crossBD - crossDE;

    if (std::abs(static_cast<double>(denom)) < 1e-15) return std::nullopt;

    const long double beta = (K - crossBD - crossDE) / denom;
    if (!std::isfinite(static_cast<double>(beta))) return std::nullopt;

    const double oneMinus = 1.0 - static_cast<double>(beta);
    if (std::abs(oneMinus) < 1e-15) return std::nullopt;

    const Point Dp{ D.x + static_cast<double>(beta) * (E.x - D.x),
                    D.y + static_cast<double>(beta) * (E.y - D.y) };

    // Displacement cost = |triangle BCD| * |beta / (1 - beta)|
    const double cost = area2TriangleAbs(B, C, D) *
                        std::abs(static_cast<double>(beta) / oneMinus);
    return std::make_pair(Dp, cost);
}

// -------------------------------------------------------------------------
// Local topology check
// -------------------------------------------------------------------------
// After collapsing vertex C (at node index idxC in ring r) and moving its
// neighbour to movedPt, check that:
//   1. The two new edges (prev->movedPt and movedPt->next, or the symmetric
//      pair for move-next) do not intersect any other edge of the same ring
//      or any edge of any other ring.
//   2. Every hole (ring index > 0) still has at least one vertex strictly
//      inside the outer ring (ring index 0).
//
// This is O(n) per check instead of O(n^2) because we only test the two
// new edges rather than rebuilding and re-validating the entire polygon.

static bool localTopologyOk(
    const std::vector<Ring>& rings,
    int                       ringIdx,   // which ring is being modified
    std::size_t               idxC,      // node index of the vertex being removed
    std::size_t               idxMoved,  // node index of the vertex being moved
    const Point&              movedPt)   // new position of idxMoved
{
    const Ring& rr = rings[static_cast<std::size_t>(ringIdx)];

    // Determine the two new edges produced by this collapse.
    // If we are moving the predecessor (move_prev):  new edges are prev(idxMoved)->movedPt
    //                                                 and movedPt->next(idxC)
    // If we are moving the successor (move_next):    new edges are prev(idxC)->movedPt
    //                                                 and movedPt->next(idxMoved)
    const std::size_t prevOfMoved = rr.nodes[idxMoved].prev;
    const std::size_t nextOfC     = rr.nodes[idxC].next;
    const std::size_t prevOfC     = rr.nodes[idxC].prev;
    const std::size_t nextOfMoved = rr.nodes[idxMoved].next;

    // Decide which edge pair to test based on whether idxMoved == prev(idxC)
    Point edgeA1, edgeA2, edgeB1, edgeB2;
    if (idxMoved == rr.nodes[idxC].prev) {
        // move_prev: predecessor is being moved
        edgeA1 = rr.nodes[prevOfMoved].p;  edgeA2 = movedPt;
        edgeB1 = movedPt;                   edgeB2 = rr.nodes[nextOfC].p;
    } else {
        // move_next: successor is being moved
        edgeA1 = rr.nodes[prevOfC].p;      edgeA2 = movedPt;
        edgeB1 = movedPt;                   edgeB2 = rr.nodes[nextOfMoved].p;
    }

    // Collect all other edges of the modified ring (excluding the 3 old edges
    // that are being replaced: prev(idxMoved)->idxMoved, idxMoved->idxC,
    // idxC->next(idxC)  [or prev(idxC)->idxC, idxC->idxMoved, idxMoved->next])
    // We build the set of "old" node pairs to skip.
    auto skipEdge = [&](std::size_t u, std::size_t v) -> bool {
        // The 3 edges that vanish: (prevOfMoved,idxMoved), (idxMoved,idxC),
        // (idxC,nextOfC) for move_prev, symmetric for move_next.
        if (idxMoved == rr.nodes[idxC].prev) {
            return (u == prevOfMoved && v == idxMoved) ||
                   (u == idxMoved   && v == idxC)      ||
                   (u == idxC       && v == nextOfC);
        } else {
            return (u == prevOfC   && v == idxC)      ||
                   (u == idxC      && v == idxMoved)   ||
                   (u == idxMoved  && v == nextOfMoved);
        }
    };

    // Test each new edge against every surviving edge of the modified ring,
    // skipping the 3 old edges and skipping the adjacent edges (which share
    // an endpoint with the new edge).
    std::size_t cur = rr.head;
    for (std::size_t k = 0; k < rr.size; ++k, cur = rr.nodes[cur].next) {
        if (cur == idxC) continue;            // this node is being removed
        const std::size_t nxt = rr.nodes[cur].next == idxC
                                ? rr.nodes[idxC].next  // skip over removed node
                                : rr.nodes[cur].next;
        if (nxt == idxC) continue;

        if (skipEdge(cur, nxt)) continue;

        const Point& ep = rr.nodes[cur].p;
        const Point& eq = (nxt == idxMoved) ? movedPt : rr.nodes[nxt].p;

        // Skip edges that share an endpoint with either new edge
        // (shared endpoints are not a crossing, just adjacency)
        auto sharesEndpoint = [&](const Point& a1, const Point& a2,
                                  const Point& b1, const Point& b2) {
            return nearlyEqual(a1.x, b1.x) && nearlyEqual(a1.y, b1.y) ||
                   nearlyEqual(a1.x, b2.x) && nearlyEqual(a1.y, b2.y) ||
                   nearlyEqual(a2.x, b1.x) && nearlyEqual(a2.y, b1.y) ||
                   nearlyEqual(a2.x, b2.x) && nearlyEqual(a2.y, b2.y);
        };

        if (!sharesEndpoint(edgeA1, edgeA2, ep, eq) &&
            segmentsIntersect(edgeA1, edgeA2, ep, eq)) return false;
        if (!sharesEndpoint(edgeB1, edgeB2, ep, eq) &&
            segmentsIntersect(edgeB1, edgeB2, ep, eq)) return false;
    }

    // Test both new edges against every edge of every OTHER ring.
    for (std::size_t ri = 0; ri < rings.size(); ++ri) {
        if (static_cast<int>(ri) == ringIdx) continue;
        const Ring& other = rings[ri];
        std::size_t oc = other.head;
        for (std::size_t k = 0; k < other.size; ++k, oc = other.nodes[oc].next) {
            const std::size_t on = other.nodes[oc].next;
            const Point& ep = other.nodes[oc].p;
            const Point& eq = other.nodes[on].p;
            if (segmentsIntersect(edgeA1, edgeA2, ep, eq)) return false;
            if (segmentsIntersect(edgeB1, edgeB2, ep, eq)) return false;
        }
    }

    // If this is a hole (ringIdx > 0), verify it still lies inside the outer ring.
    // We use the first alive node of the hole as the test point.
    if (ringIdx > 0 && !rings.empty()) {
        // Rebuild the outer ring temporarily with no modification (it is unchanged).
        const Ring& outer = rings[0];
        std::vector<Vertex> outerVerts;
        outerVerts.reserve(outer.size);
        std::size_t oc = outer.head;
        for (std::size_t k = 0; k < outer.size; ++k, oc = outer.nodes[oc].next)
            outerVerts.push_back(Vertex{outer.nodes[oc].p, outer.nodes[oc].original_id});

        // Use the moved point itself as a representative test point.
        if (!pointInPolygonStrict(movedPt, outerVerts)) return false;
    }

    // If this is the outer ring (ringIdx == 0), verify every hole still lies inside.
    if (ringIdx == 0) {
        // Build a temporary flat representation of the modified outer ring.
        std::vector<Vertex> outerVerts;
        outerVerts.reserve(rings[0].size - 1);
        std::size_t cur2 = rings[0].head;
        for (std::size_t k = 0; k < rings[0].size; ++k, cur2 = rings[0].nodes[cur2].next) {
            if (cur2 == idxC) continue;
            Point pt = (cur2 == idxMoved) ? movedPt : rings[0].nodes[cur2].p;
            outerVerts.push_back(Vertex{pt, rings[0].nodes[cur2].original_id});
        }
        for (std::size_t ri = 1; ri < rings.size(); ++ri) {
            const Point& sample = rings[ri].nodes[rings[ri].head].p;
            if (!pointInPolygonStrict(sample, outerVerts)) return false;
        }
    }

    return true;
}

// -------------------------------------------------------------------------
// Priority-queue entry (heap node)
// -------------------------------------------------------------------------
// Each entry represents one candidate collapse operation.
// The generation field lets us lazily discard stale entries: if
// entry.gen != ring.nodes[entry.idxC].generation (or the moved node's
// generation), the entry is outdated and must be skipped.

struct HeapEntry {
    double      cost{};
    int         ring_index{};
    std::size_t idxC{};        // index of the vertex to be removed
    std::size_t idxMoved{};    // index of the vertex to be slid
    bool        move_prev{};   // true = slide predecessor, false = slide successor
    Point       moved_pt{};    // pre-computed new position
    int         gen_c{};       // generation of node idxC at insertion time
    int         gen_moved{};   // generation of node idxMoved at insertion time
    int         orig_id_c{};   // original_id of idxC (for tie-breaking)

    // Min-heap: smallest cost at top.
    bool operator>(const HeapEntry& o) const {
        if (!nearlyEqual(cost, o.cost, 1e-12)) return cost > o.cost;
        // Tie-break: prefer lower ring_id, then lower original_id of removed vertex.
        if (ring_index != o.ring_index) return ring_index > o.ring_index;
        return orig_id_c > o.orig_id_c;
    }
};

using MinHeap = std::priority_queue<HeapEntry,
                                    std::vector<HeapEntry>,
                                    std::greater<HeapEntry>>;

// Push both candidate operations (move_prev and move_next) for the vertex
// at node index idxC into the heap, provided they pass basic sanity checks.
static void pushCandidates(MinHeap&                    heap,
                           const std::vector<Ring>&    rings,
                           int                         ringIdx,
                           std::size_t                 idxC) {
    const Ring& r  = rings[static_cast<std::size_t>(ringIdx)];
    if (!r.nodes[idxC].alive) return;
    if (r.nodes[idxC].original_id == 0) return; // anchor vertex: never remove

    const int minV = ringMinVertices(r.ring_id);
    if (static_cast<int>(r.size) <= minV) return; // ring too small already

    const std::size_t idxB = r.nodes[idxC].prev;  // predecessor
    const std::size_t idxD = r.nodes[idxC].next;  // successor
    const std::size_t idxA = r.nodes[idxB].prev;  // predecessor of predecessor
    const std::size_t idxE = r.nodes[idxD].next;  // successor of successor

    const Point& A = r.nodes[idxA].p;
    const Point& B = r.nodes[idxB].p;
    const Point& C = r.nodes[idxC].p;
    const Point& D = r.nodes[idxD].p;
    const Point& E = r.nodes[idxE].p;

    // move_prev: remove C, slide B to B'
    if (auto mv = computeMovePrev(A, B, C, D)) {
        HeapEntry e;
        e.cost       = mv->second;
        e.ring_index = ringIdx;
        e.idxC       = idxC;
        e.idxMoved   = idxB;
        e.move_prev  = true;
        e.moved_pt   = mv->first;
        e.gen_c      = r.nodes[idxC].generation;
        e.gen_moved  = r.nodes[idxB].generation;
        e.orig_id_c  = r.nodes[idxC].original_id;
        heap.push(e);
    }

    // move_next: remove C, slide D to D'
    if (auto mv = computeMoveNext(B, C, D, E)) {
        HeapEntry e;
        e.cost       = mv->second;
        e.ring_index = ringIdx;
        e.idxC       = idxC;
        e.idxMoved   = idxD;
        e.move_prev  = false;
        e.moved_pt   = mv->first;
        e.gen_c      = r.nodes[idxC].generation;
        e.gen_moved  = r.nodes[idxD].generation;
        e.orig_id_c  = r.nodes[idxC].original_id;
        heap.push(e);
    }
}

// -------------------------------------------------------------------------
// CSV parsing
// -------------------------------------------------------------------------

static inline std::vector<std::string> splitCsvLine(const std::string& line) {
    std::vector<std::string> parts;
    std::stringstream ss(line);
    std::string item;
    while (std::getline(ss, item, ',')) parts.push_back(item);
    return parts;
}

// Reads the CSV and returns rings sorted by ring_id with the outer ring
// (ring_id == 0) guaranteed to be first.
static bool parseInput(const std::string&               path,
                       std::vector<int>&                ringIdsOut,
                       std::vector<std::vector<Vertex>>& ringsOut) {
    std::ifstream in(path);
    if (!in) return false;

    std::string line;
    if (!std::getline(in, line)) return false; // skip header

    std::map<int, std::map<int, Point>> byRing;
    while (std::getline(in, line)) {
        if (line.empty()) continue;
        const auto parts = splitCsvLine(line);
        if (parts.size() < 4) continue;
        const int    rid = std::stoi(parts[0]);
        const int    vid = std::stoi(parts[1]);
        const double x   = std::stod(parts[2]);
        const double y   = std::stod(parts[3]);
        byRing[rid][vid] = Point{x, y};
    }

    ringIdsOut.clear();
    ringsOut.clear();
    for (auto& [rid, verts] : byRing) {
        ringIdsOut.push_back(rid);
        std::vector<Vertex> ring;
        ring.reserve(verts.size());
        for (auto& [vid, p] : verts) ring.push_back(Vertex{p, vid});
        ringsOut.push_back(std::move(ring));
    }

    // Move ring_id==0 to index 0
    if (!ringsOut.empty() && ringIdsOut[0] != 0) {
        auto it = std::find(ringIdsOut.begin(), ringIdsOut.end(), 0);
        if (it != ringIdsOut.end()) {
            const std::size_t idx =
                static_cast<std::size_t>(std::distance(ringIdsOut.begin(), it));
            std::swap(ringIdsOut[0], ringIdsOut[idx]);
            std::swap(ringsOut[0],   ringsOut[idx]);
        }
    }
    return true;
}

} // namespace

// =========================================================================
// main
// =========================================================================
int main(int argc, char** argv) {
    if (argc < 3) {
        std::cerr << "Usage: " << (argc > 0 ? argv[0] : "simplify")
                  << " <input_file.csv> <target_vertices>\n";
        return 1;
    }

    const std::string inputPath = argv[1];
    const std::size_t target    =
        static_cast<std::size_t>(std::stoll(argv[2]));

    // ---- Parse input ----
    std::vector<int>                ringIds;
    std::vector<std::vector<Vertex>> flatRings;
    if (!parseInput(inputPath, ringIds, flatRings)) {
        std::cerr << "Failed to read input file: " << inputPath << "\n";
        return 1;
    }

    // ---- Compute input area (before any changes) ----
    const double inputArea = [&]() {
        double s = 0.0;
        for (const auto& r : flatRings) s += signedRingArea(r);
        return s;
    }();

    // ---- Build doubly-linked ring structures ----
    std::vector<Ring> rings;
    rings.reserve(flatRings.size());
    for (std::size_t i = 0; i < flatRings.size(); ++i)
        rings.push_back(buildRing(flatRings[i], ringIds[i]));

    std::size_t totalVerts = totalVertexCount(flatRings);

    // ---- Populate initial priority queue ----
    // For every vertex in every ring, compute both candidate operations and
    // push them into the min-heap.  O(n log n) total.
    MinHeap heap;
    for (std::size_t ri = 0; ri < rings.size(); ++ri) {
        std::size_t cur = rings[ri].head;
        for (std::size_t k = 0; k < rings[ri].size; ++k, cur = rings[ri].nodes[cur].next)
            pushCandidates(heap, rings, static_cast<int>(ri), cur);
    }

    double totalArealDisplacement = 0.0;

    // ---- Main simplification loop ----
    // Each iteration pops the cheapest valid entry from the heap, applies it,
    // then re-inserts only the ~4 affected neighbours.  O(log n) per step.
    while (totalVerts > target && !heap.empty()) {
        // Pop the cheapest candidate
        HeapEntry e = heap.top();
        heap.pop();

        const std::size_t ri = static_cast<std::size_t>(e.ring_index);
        Ring& ring = rings[ri];

        // ---- Lazy deletion: skip stale entries ----
        // An entry is stale if the node it references has been moved or removed
        // since the entry was created (detected via the generation counter).
        if (!ring.nodes[e.idxC].alive)                           continue;
        if (ring.nodes[e.idxC].generation    != e.gen_c)         continue;
        if (!ring.nodes[e.idxMoved].alive)                       continue;
        if (ring.nodes[e.idxMoved].generation != e.gen_moved)    continue;

        // ---- Minimum size guard ----
        if (static_cast<int>(ring.size) <= ringMinVertices(ring.ring_id)) continue;

        // ---- Local topology check ----
        if (!localTopologyOk(rings, e.ring_index, e.idxC, e.idxMoved, e.moved_pt))
            continue;

        // ---- Apply the collapse ----
        totalArealDisplacement += e.cost;

        // Move the neighbour to its new Steiner point and increment its generation
        // so any existing heap entries for it become stale.
        ring.nodes[e.idxMoved].p = e.moved_pt;
        ring.nodes[e.idxMoved].generation++;

        // Unlink idxC from the doubly-linked list and mark it dead.
        const std::size_t prevC = ring.nodes[e.idxC].prev;
        const std::size_t nextC = ring.nodes[e.idxC].next;
        ring.nodes[prevC].next  = nextC;
        ring.nodes[nextC].prev  = prevC;
        ring.nodes[e.idxC].alive = false;
        ring.nodes[e.idxC].generation++;  // stale any heap entries for idxC

        // Update head if we just removed the head node.
        if (ring.head == e.idxC) ring.head = nextC;
        ring.size--;
        totalVerts--;

        // ---- Local update: re-insert candidates for the ~4 affected neighbours ----
        // Only the nodes whose 4-vertex window changed need new entries.
        // Those are: prevprev, prev (=idxMoved), next, nextnext of the removed vertex.
        const std::size_t affected[] = {
            ring.nodes[e.idxMoved].prev,   // A (prev of moved)
            e.idxMoved,                     // moved node itself (B or D)
            nextC,                          // first node after the removed one
            ring.nodes[nextC].next          // one further
        };
        for (std::size_t nodeIdx : affected) {
            if (ring.nodes[nodeIdx].alive)
                pushCandidates(heap, rings, e.ring_index, nodeIdx);
        }
    }

    // ---- Flatten rings back to vertex vectors ----
    std::vector<std::vector<Vertex>> outRings;
    outRings.reserve(rings.size());
    for (const auto& r : rings)
        outRings.push_back(flattenRing(r));

    // ---- Compute output area ----
    const double outputArea = [&]() {
        double s = 0.0;
        for (const auto& r : outRings) s += signedRingArea(r);
        return s;
    }();

    // ---- Print output ----
    std::cout << "ring_id,vertex_id,x,y\n";
    std::cout << std::setprecision(11) << std::defaultfloat;
    for (std::size_t ri = 0; ri < outRings.size(); ++ri) {
        const int ring_id  = ringIds[ri];
        const auto& ring   = outRings[ri];
        for (std::size_t vi = 0; vi < ring.size(); ++vi)
            std::cout << ring_id << "," << vi << ","
                      << ring[vi].p.x << "," << ring[vi].p.y << "\n";
    }

    std::cout << std::scientific << std::setprecision(6);
    std::cout << "Total signed area in input: "  << inputArea              << "\n";
    std::cout << "Total signed area in output: " << outputArea             << "\n";
    std::cout << "Total areal displacement: "    << totalArealDisplacement << "\n";

    return 0;
}
