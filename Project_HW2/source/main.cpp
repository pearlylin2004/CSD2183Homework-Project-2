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
// KEY IMPROVEMENTS over the previous version:
//
// 1. DOUBLY-LINKED RING (RingNode):
//    Each ring is stored as a circular doubly-linked list so that removing
//    a vertex and navigating to neighbours is O(1) instead of O(n) shifting.
//
// 2. GENERATION COUNTERS (true lazy deletion):
//    Every node carries a generation counter. HeapEntry records the generation
//    of both the removed node and the moved node at insertion time. When an
//    entry is popped, mismatched generations discard it instantly as stale.
//    Previously only original_id was used, which could miss cases where a
//    moved vertex retains its original_id.
//
// 3. LOCAL RE-ENQUEUE (O(log n) per collapse instead of O(n)):
//    After each collapse only the ~4 nodes whose 4-vertex windows changed
//    are re-pushed into the heap. Previously the entire ring was re-enqueued
//    (O(n) per step), making the main loop O(n^2 log n) overall.
//    With local updates the loop is O(n log n).
//
// 4. LOCAL TOPOLOGY CHECK (O(n) instead of O(n^2)):
//    Instead of rebuilding full ring copies and calling ringIsSimple +
//    ringsAreDisjoint, we test only the two new edges (AE and ED) against
//    every other segment. This avoids the O(n^2) full simplicity scan.

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

// -------------------------------------------------------------------------
// Numeric constants
// -------------------------------------------------------------------------
constexpr double kEps = 1e-12;

// -------------------------------------------------------------------------
// Basic geometry types
// -------------------------------------------------------------------------

struct Point {
    double x{};
    double y{};
};

// -------------------------------------------------------------------------
// Low-level geometry helpers
// -------------------------------------------------------------------------

static inline bool nearlyEqual(double a, double b, double eps = kEps) {
    return std::abs(a - b) <= eps;
}

// Cross product a x b in long double for numerical stability.
static inline long double crossLD(const Point& a, const Point& b) {
    return static_cast<long double>(a.x) * static_cast<long double>(b.y)
         - static_cast<long double>(a.y) * static_cast<long double>(b.x);
}

// Cross product of (b-a) and (c-a): twice the signed area of triangle abc.
static inline long double crossLD(const Point& a, const Point& b, const Point& c) {
    return crossLD(Point{b.x - a.x, b.y - a.y}, Point{c.x - a.x, c.y - a.y});
}

// Twice the unsigned area of triangle abc.
static inline double area2TriangleAbs(const Point& a, const Point& b, const Point& c) {
    return static_cast<double>(std::abs(crossLD(a, b, c)));
}

// Shoelace formula: signed area of a closed ring (CCW = positive).
static inline double signedRingArea(const std::vector<Point>& pts) {
    if (pts.size() < 3) return 0.0;
    long double sum = 0.0L;
    const std::size_t n = pts.size();
    for (std::size_t i = 0; i < n; ++i)
        sum += crossLD(pts[i], pts[(i + 1) % n]);
    return static_cast<double>(0.5L * sum);
}

// True if point p lies on segment [a, b].
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

// True if segments (p1,q1) and (p2,q2) share any point.
static inline bool segmentsIntersectProperOrTouch(const Point& p1, const Point& q1,
                                                   const Point& p2, const Point& q2) {
    const int o1 = orient(p1, q1, p2), o2 = orient(p1, q1, q2);
    const int o3 = orient(p2, q2, p1), o4 = orient(p2, q2, q1);
    if (o1 == 0 && onSegment(p1, q1, p2)) return true;
    if (o2 == 0 && onSegment(p1, q1, q2)) return true;
    if (o3 == 0 && onSegment(p2, q2, p1)) return true;
    if (o4 == 0 && onSegment(p2, q2, q1)) return true;
    return (o1 != o2) && (o3 != o4);
}

// Ray-casting point-in-polygon (strict: boundary returns false).
static inline bool pointInPolygonStrict(const Point& p, const std::vector<Point>& ring) {
    if (ring.size() < 3) return false;
    bool inside = false;
    for (std::size_t i = 0, j = ring.size() - 1; i < ring.size(); j = i++) {
        const Point& a = ring[j];
        const Point& b = ring[i];
        if (onSegment(a, b, p)) return false;
        if (((a.y > p.y) != (b.y > p.y)) &&
            (p.x < (b.x - a.x) * (p.y - a.y) / (b.y - a.y) + a.x))
            inside = !inside;
    }
    return inside;
}

// Minimum vertices a ring must keep (a triangle is valid for any ring).
static inline int ringMinVertices() {
    return 3;  // a triangle is the minimum valid ring for both exterior and interior
}

// -------------------------------------------------------------------------
// Doubly-linked ring
// -------------------------------------------------------------------------
// Stores each ring as a pool of nodes with stable integer indices and O(1)
// prev/next navigation. Removing a node unlinks it and marks it dead;
// the pool is never compacted so indices remain valid throughout.

struct RingNode {
    Point       p{};
    int         original_id{};
    int         generation{0};   // incremented whenever this node is moved or removed
    std::size_t prev{};
    std::size_t next{};
    bool        alive{true};
};

struct Ring {
    std::vector<RingNode> nodes;   // stable-index node pool
    std::size_t           head{};  // index of the first alive node
    std::size_t           size{};  // number of alive nodes
    int                   ring_id{};
};

// Build a Ring from a flat list of (Point, original_id) pairs.
static Ring buildRing(const std::vector<std::pair<Point, int>>& verts, int ring_id) {
    Ring r;
    r.ring_id = ring_id;
    r.size    = verts.size();
    r.nodes.resize(verts.size());
    for (std::size_t i = 0; i < verts.size(); ++i) {
        r.nodes[i].p           = verts[i].first;
        r.nodes[i].original_id = verts[i].second;
        r.nodes[i].prev        = (i + verts.size() - 1) % verts.size();
        r.nodes[i].next        = (i + 1) % verts.size();
    }
    r.head = 0;
    return r;
}

// Flatten a Ring to a vector of Points (used for area calculation).
static std::vector<Point> ringToPoints(const Ring& ring) {
    std::vector<Point> pts;
    pts.reserve(ring.size);
    std::size_t cur = ring.head;
    for (std::size_t k = 0; k < ring.size; ++k, cur = ring.nodes[cur].next)
        pts.push_back(ring.nodes[cur].p);
    return pts;
}

// -------------------------------------------------------------------------
// Area-preserving placement (Kronenfeld et al. 2020)
// -------------------------------------------------------------------------
// For a 4-vertex window A-B-C-D, find the Steiner point that:
//   (a) preserves the ring's signed area after removing C, and
//   (b) minimises the resulting areal displacement.
//
// computeMovePrev: remove C, slide B to B' on ray A->B.
// computeMoveNext: remove C, slide D to D' on ray D->E.
// Both return (new_point, cost) or nullopt if the geometry is degenerate.

static inline Opt<std::pair<Point, double>>
computeMovePrev(const Point& A, const Point& B, const Point& C, const Point& D) {
    // K = sum of the three shoelace terms being replaced.
    const long double crossAB = crossLD(A, B);
    const long double crossBC = crossLD(B, C);
    const long double crossCD = crossLD(C, D);
    const long double K       = crossAB + crossBC + crossCD;

    // Solve for parameter t so that placing B' = A + t*(B-A) preserves area.
    const long double crossAD = crossLD(A, D);
    const long double crossBD = crossLD(B, D);
    const long double denom   = crossAB + crossBD - crossAD;

    if (std::abs(static_cast<double>(denom)) < 1e-15) return std::nullopt;
    const long double t = (K - crossAD) / denom;
    if (!std::isfinite(static_cast<double>(t)) ||
        std::abs(static_cast<double>(t)) < 1e-15 ||
        static_cast<double>(t) < 0.0) return std::nullopt;

    const Point Bp{ A.x + static_cast<double>(t) * (B.x - A.x),
                    A.y + static_cast<double>(t) * (B.y - A.y) };
    const double cost = area2TriangleAbs(B, C, D) *
                        std::abs(1.0 - 1.0 / static_cast<double>(t));
    return std::make_pair(Bp, cost);
}

static inline Opt<std::pair<Point, double>>
computeMoveNext(const Point& B, const Point& C, const Point& D, const Point& E) {
    const long double crossBC = crossLD(B, C);
    const long double crossCD = crossLD(C, D);
    const long double crossDE = crossLD(D, E);
    const long double K       = crossBC + crossCD + crossDE;

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
    const double cost = area2TriangleAbs(B, C, D) *
                        std::abs(static_cast<double>(beta) / oneMinus);
    return std::make_pair(Dp, cost);
}

// -------------------------------------------------------------------------
// Local topology check  (O(n) instead of O(n^2))
// -------------------------------------------------------------------------
// After collapsing node idxC and moving node idxMoved to movedPt, only the
// two new edges need to be tested — not the entire polygon.
// This replaces the old topologyOkAfterApplying which rebuilt full ring copies
// and called ringIsSimple (O(n^2)) on every candidate.

static bool localTopologyOk(const std::vector<Ring>& rings,
                             int         ringIdx,
                             std::size_t idxC,
                             std::size_t idxMoved,
                             const Point& movedPt)
{
    const Ring& rr      = rings[static_cast<std::size_t>(ringIdx)];
    const bool movePrev = (idxMoved == rr.nodes[idxC].prev);

    // The two new edges produced by this collapse:
    //   move_prev: prev(idxMoved)->movedPt  and  movedPt->next(idxC)
    //   move_next: prev(idxC)->movedPt      and  movedPt->next(idxMoved)
    Point eA1, eA2, eB1, eB2;
    if (movePrev) {
        eA1 = rr.nodes[rr.nodes[idxMoved].prev].p;  eA2 = movedPt;
        eB1 = movedPt;  eB2 = rr.nodes[rr.nodes[idxC].next].p;
    } else {
        eA1 = rr.nodes[rr.nodes[idxC].prev].p;       eA2 = movedPt;
        eB1 = movedPt;  eB2 = rr.nodes[rr.nodes[idxMoved].next].p;
    }

    // Returns true if two segments share an endpoint (adjacency, not crossing).
    auto sharesEndpoint = [&](const Point& a1, const Point& a2,
                              const Point& b1, const Point& b2) -> bool {
        return (nearlyEqual(a1.x,b1.x)&&nearlyEqual(a1.y,b1.y)) ||
               (nearlyEqual(a1.x,b2.x)&&nearlyEqual(a1.y,b2.y)) ||
               (nearlyEqual(a2.x,b1.x)&&nearlyEqual(a2.y,b1.y)) ||
               (nearlyEqual(a2.x,b2.x)&&nearlyEqual(a2.y,b2.y));
    };

    // Test each new edge against every surviving edge of the modified ring.
    std::size_t cur = rr.head;
    for (std::size_t k = 0; k < rr.size; ++k, cur = rr.nodes[cur].next) {
        if (cur == idxC) continue;

        std::size_t nxt = rr.nodes[cur].next;
        if (nxt == idxC) nxt = rr.nodes[idxC].next;
        if (nxt == idxC) continue;

        const Point ep = rr.nodes[cur].p;
        const Point eq = (nxt == idxMoved) ? movedPt : rr.nodes[nxt].p;

        if (!sharesEndpoint(eA1,eA2,ep,eq) &&
            segmentsIntersectProperOrTouch(eA1,eA2,ep,eq)) return false;
        if (!sharesEndpoint(eB1,eB2,ep,eq) &&
            segmentsIntersectProperOrTouch(eB1,eB2,ep,eq)) return false;
    }

    // Test new edges against every edge of every other ring.
    for (std::size_t ri = 0; ri < rings.size(); ++ri) {
        if (static_cast<int>(ri) == ringIdx) continue;
        const Ring& other = rings[ri];
        std::size_t oc = other.head;
        for (std::size_t k = 0; k < other.size; ++k, oc = other.nodes[oc].next) {
            const Point& ep = other.nodes[oc].p;
            const Point& eq = other.nodes[other.nodes[oc].next].p;
            if (!sharesEndpoint(eA1,eA2,ep,eq) && segmentsIntersectProperOrTouch(eA1,eA2,ep,eq)) return false;
            if (!sharesEndpoint(eB1,eB2,ep,eq) && segmentsIntersectProperOrTouch(eB1,eB2,ep,eq)) return false;
        }
    }

    // Hole containment: if a hole is being modified, its moved vertex must
    // still be strictly inside the outer ring.
    if (ringIdx > 0 && rings.size() > 0) {
        const std::vector<Point> outerPts = ringToPoints(rings[0]);
        if (!pointInPolygonStrict(movedPt, outerPts)) return false;
    }

    // If the outer ring is modified, check all holes are still contained.
    if (ringIdx == 0) {
        std::vector<Point> outerPts;
        outerPts.reserve(rr.size - 1);
        std::size_t c2 = rr.head;
        for (std::size_t k = 0; k < rr.size; ++k, c2 = rr.nodes[c2].next) {
            if (c2 == idxC) continue;
            outerPts.push_back((c2 == idxMoved) ? movedPt : rr.nodes[c2].p);
        }
        for (std::size_t ri = 1; ri < rings.size(); ++ri) {
            const Point& sample = rings[ri].nodes[rings[ri].head].p;
            if (!pointInPolygonStrict(sample, outerPts)) return false;
        }
    }

    return true;
}

// -------------------------------------------------------------------------
// Priority-queue entry
// -------------------------------------------------------------------------
// gen_c and gen_moved allow true lazy deletion: if either node has been
// touched since this entry was created, the entry is stale and discarded.

struct HeapEntry {
    double      cost{};
    int         ring_index{};
    std::size_t idxC{};        // node to remove
    std::size_t idxMoved{};    // node to slide
    bool        move_prev{};
    Point       moved_pt{};
    int         gen_c{};       // generation of idxC at insertion
    int         gen_moved{};   // generation of idxMoved at insertion
    int         orig_id_c{};   // for deterministic tie-breaking

    bool operator>(const HeapEntry& o) const {
        if (!nearlyEqual(cost, o.cost, 1e-12)) return cost > o.cost;
        if (ring_index != o.ring_index)        return ring_index > o.ring_index;
        return orig_id_c > o.orig_id_c;
    }
};

using MinHeap = std::priority_queue<HeapEntry,
                                    std::vector<HeapEntry>,
                                    std::greater<HeapEntry>>;

// Push both candidate operations for node idxC into the heap.
static void pushCandidates(MinHeap&                 heap,
                           const std::vector<Ring>& rings,
                           int                      ringIdx,
                           std::size_t              idxC)
{
    const Ring& r = rings[static_cast<std::size_t>(ringIdx)];
    if (!r.nodes[idxC].alive)            return;

    const std::size_t idxB = r.nodes[idxC].prev;
    const std::size_t idxD = r.nodes[idxC].next;
    const std::size_t idxA = r.nodes[idxB].prev;
    const std::size_t idxE = r.nodes[idxD].next;

    const Point& A = r.nodes[idxA].p;
    const Point& B = r.nodes[idxB].p;
    const Point& C = r.nodes[idxC].p;
    const Point& D = r.nodes[idxD].p;
    const Point& E = r.nodes[idxE].p;

    // move_prev: remove C, slide B -> B'
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

    // move_next: remove C, slide D -> D'
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

static bool parseInput(const std::string& path,
                       std::vector<int>&  ringIdsOut,
                       std::vector<std::vector<std::pair<Point,int>>>& ringsOut)
{
    std::ifstream in(path);
    if (!in) return false;
    std::string line;
    if (!std::getline(in, line)) return false;  // skip header

    std::map<int, std::map<int, Point>> byRing;
    while (std::getline(in, line)) {
        if (line.empty()) continue;
        const auto parts = splitCsvLine(line);
        if (parts.size() < 4) continue;
        byRing[std::stoi(parts[0])][std::stoi(parts[1])] =
            Point{std::stod(parts[2]), std::stod(parts[3])};
    }

    ringIdsOut.clear();
    ringsOut.clear();
    for (auto& [rid, verts] : byRing) {
        ringIdsOut.push_back(rid);
        std::vector<std::pair<Point,int>> ring;
        ring.reserve(verts.size());
        for (auto& [vid, p] : verts) ring.emplace_back(p, vid);
        ringsOut.push_back(std::move(ring));
    }

    // Ensure outer ring (ring_id==0) is at index 0.
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

}  // namespace

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
    const std::size_t target    = static_cast<std::size_t>(std::stoll(argv[2]));

    // ---- Parse input ----
    std::vector<int> ringIds;
    std::vector<std::vector<std::pair<Point,int>>> rawRings;
    if (!parseInput(inputPath, ringIds, rawRings)) {
        std::cerr << "Failed to read input file: " << inputPath << "\n";
        return 1;
    }

    // ---- Compute input area before any changes ----
    const double inputArea = [&]() {
        double s = 0.0;
        for (const auto& rv : rawRings) {
            std::vector<Point> pts;
            for (auto& [p, id] : rv) pts.push_back(p);
            s += signedRingArea(pts);
        }
        return s;
    }();

    // ---- Build doubly-linked rings ----
    std::vector<Ring> rings;
    rings.reserve(rawRings.size());
    for (std::size_t i = 0; i < rawRings.size(); ++i)
        rings.push_back(buildRing(rawRings[i], ringIds[i]));

    std::size_t totalVerts = 0;
    for (const auto& r : rings) totalVerts += r.size;

    // ---- Populate the initial heap ----
    // Push both candidates for every non-anchor vertex in every ring.
    MinHeap heap;
    for (std::size_t ri = 0; ri < rings.size(); ++ri) {
        std::size_t cur = rings[ri].head;
        for (std::size_t k = 0; k < rings[ri].size;
             ++k, cur = rings[ri].nodes[cur].next)
            pushCandidates(heap, rings, static_cast<int>(ri), cur);
    }

    double totalArealDisplacement = 0.0;

    // ---- Main greedy loop ----
    // Each iteration pops the cheapest valid entry and applies it in O(log n).
    // Only the ~4 affected neighbours are re-pushed (local update).
    while (totalVerts > target && !heap.empty()) {
        HeapEntry e = heap.top();
        heap.pop();

        const std::size_t ri = static_cast<std::size_t>(e.ring_index);
        Ring& ring = rings[ri];

        // ---- Lazy deletion via generation counters ----
        // If either node was moved or removed since this entry was created,
        // its generation will not match — discard the entry immediately.
        if (!ring.nodes[e.idxC].alive)                         continue;
        if (ring.nodes[e.idxC].generation    != e.gen_c)       continue;
        if (!ring.nodes[e.idxMoved].alive)                     continue;
        if (ring.nodes[e.idxMoved].generation != e.gen_moved)  continue;

        // Minimum size guard.
        if (static_cast<int>(ring.size) <= ringMinVertices()) continue;

        // ---- Local topology check ----
        // Tests only the 2 new edges instead of rebuilding the full polygon.
        if (!localTopologyOk(rings, e.ring_index, e.idxC, e.idxMoved, e.moved_pt))
            continue;

        // ---- Apply the collapse ----
        totalArealDisplacement += e.cost;

        // Slide the neighbour to its new Steiner point and bump its generation
        // so that all existing heap entries for it become stale.
        ring.nodes[e.idxMoved].p = e.moved_pt;
        ring.nodes[e.idxMoved].generation++;

        // Unlink idxC from the circular list and mark it dead.
        const std::size_t prevC = ring.nodes[e.idxC].prev;
        const std::size_t nextC = ring.nodes[e.idxC].next;
        ring.nodes[prevC].next  = nextC;
        ring.nodes[nextC].prev  = prevC;
        ring.nodes[e.idxC].alive      = false;
        ring.nodes[e.idxC].generation++;  // stale all heap entries for idxC

        if (ring.head == e.idxC) ring.head = nextC;
        ring.size--;
        totalVerts--;

        // ---- Local re-enqueue: only the ~4 nodes whose windows changed ----
        // This is the key improvement over the previous O(n) full-ring re-enqueue.
        // Only the nodes whose 4-vertex neighbourhood was altered need new entries.
        const std::size_t affected[] = {
            ring.nodes[e.idxMoved].prev,  // prev of the moved node (window shifted)
            e.idxMoved,                    // the moved node itself
            nextC,                          // first node after the removed vertex
            ring.nodes[nextC].next          // one step further
        };
        for (std::size_t nodeIdx : affected)
            if (ring.nodes[nodeIdx].alive)
                pushCandidates(heap, rings, e.ring_index, nodeIdx);
    }

    // ---- Flatten rings and rotate to start at original vertex 0 ----
    std::vector<std::vector<std::pair<Point,int>>> outRings;
    outRings.reserve(rings.size());
    for (const auto& r : rings) {
        std::vector<std::pair<Point,int>> flat;
        flat.reserve(r.size);
        std::size_t cur = r.head;
        for (std::size_t k = 0; k < r.size; ++k, cur = r.nodes[cur].next)
            flat.emplace_back(r.nodes[cur].p, r.nodes[cur].original_id);

        // Rotate so original_id==0 comes first; fall back to smallest surviving id.
        auto it = std::find_if(flat.begin(), flat.end(),
                               [](const std::pair<Point,int>& v){ return v.second==0; });
        if (it == flat.end())
            it = std::min_element(flat.begin(), flat.end(),
                                  [](const std::pair<Point,int>& a,
                                     const std::pair<Point,int>& b){
                                      return a.second < b.second; });
        std::rotate(flat.begin(), it, flat.end());
        outRings.push_back(std::move(flat));
    }

    // ---- Compute output area ----
    const double outputArea = [&]() {
        double s = 0.0;
        for (const auto& rv : outRings) {
            std::vector<Point> pts;
            for (auto& [p, id] : rv) pts.push_back(p);
            s += signedRingArea(pts);
        }
        return s;
    }();

    // Warn on stderr if area drifted beyond floating-point tolerance.
    if (std::abs(outputArea - inputArea) > 1e-6 * std::abs(inputArea))
        std::cerr << "WARNING: area drift: in=" << inputArea
                  << " out=" << outputArea << "\n";

    // ---- Print output to stdout ----
    std::cout << "ring_id,vertex_id,x,y\n";
    std::cout << std::setprecision(11) << std::defaultfloat;
    for (std::size_t ri = 0; ri < outRings.size(); ++ri) {
        const int ring_id = ringIds[ri];
        for (std::size_t vi = 0; vi < outRings[ri].size(); ++vi)
            std::cout << ring_id << "," << vi << ","
                      << outRings[ri][vi].first.x << ","
                      << outRings[ri][vi].first.y << "\n";
    }

    std::cout << std::scientific << std::setprecision(6);
    std::cout << "Total signed area in input: "  << inputArea              << "\n";
    std::cout << "Total signed area in output: " << outputArea             << "\n";
    std::cout << "Total areal displacement: "    << totalArealDisplacement << "\n";

    return 0;
}
