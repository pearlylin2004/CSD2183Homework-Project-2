# CSD2183 Project 2 — Area- and Topology-Preserving Polygon Simplification

## Team Members
- Jingwen
- Qi Ting
- Le Min
- Pearly

## Overview
This program simplifies a polygon (with holes) by reducing its vertex count
while preserving the exact area of each ring and maintaining topological validity,
using the Area-Preserving Segment Collapse (APSC) algorithm from Kronenfeld et al. (2020).

## Dependencies
No external libraries required. Uses C++17 standard library only.

Compiler: g++ (GCC 9 or later recommended)

## Build Instructions
```bash
make
```
This produces an executable called `simplify` in the repository root.

To clean up:
```bash
make clean
```

## Usage
```bash
./simplify <input_file.csv> <target_vertices>
```

Example:
```bash
./simplify test_cases/sample.csv 10
```

## Input Format
A CSV file with header `ring_id,vertex_id,x,y`:
- `ring_id 0` is the exterior ring (counterclockwise)
- All other ring IDs are interior rings/holes (clockwise)

## Output Format
- CSV lines for each simplified vertex
- Three summary lines: total signed area (input/output) and total areal displacement

## Test Results
| Test Case | Input Vertices | Target | Output Vertices | Area Preserved | Notes |
|---|---|---|---|---|---|
| sample.csv | 11 | 8 | 8 | ✅ | Basic example from spec |
| [add more] | | | | | |

## Algorithm
Implements APSC (Kronenfeld et al., 2020):
- For each vertex, compute the area-preserving collapse (move-prev or move-next)
- Greedily select the collapse with minimum areal displacement
- Reject any collapse that causes self-intersection or ring crossing
- Repeat until target vertex count is reached

## Reference
Kronenfeld, B. J., et al. (2020). Simplification of polylines by segment collapse:
minimizing areal displacement while preserving area.
International Journal of Cartography, 6(1), 22–46.