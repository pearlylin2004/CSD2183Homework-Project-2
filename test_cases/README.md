# Test Cases for Area-and-Topology-Preserving Polygon Simplification

Each test case consists of an **input CSV** and the corresponding **expected output**.

## Simple cases (polygons with holes)

| Input file | Vertices | Holes | Target | Output file |
|---|---|---|---|---|
| `input_rectangle_with_two_holes.csv` | 12 | 2 | 7 | `output_rectangle_with_two_holes.txt` |
| `input_cushion_with_hexagonal_hole.csv` | 22 | 1 | 13 | `output_cushion_with_hexagonal_hole.txt` |
| `input_blob_with_two_holes.csv` | 36 | 2 | 17 | `output_blob_with_two_holes.txt` |
| `input_wavy_with_three_holes.csv` | 43 | 3 | 21 | `output_wavy_with_three_holes.txt` |
| `input_lake_with_two_islands.csv` | 81 | 2 | 17 | `output_lake_with_two_islands.txt` |

## Lake cases (single polygon, no holes)

| Input file | Target | Output file |
|---|---|---|
| `input_original_01.csv` | 99 | `output_original_01.txt` |
| `input_original_02.csv` | 99 | `output_original_02.txt` |
| `input_original_03.csv` | 99 | `output_original_03.txt` |
| `input_original_04.csv` | 99 | `output_original_04.txt` |
| `input_original_05.csv` | 99 | `output_original_05.txt` |
| `input_original_06.csv` | 99 | `output_original_06.txt` |
| `input_original_07.csv` | 99 | `output_original_07.txt` |
| `input_original_08.csv` | 99 | `output_original_08.txt` |
| `input_original_09.csv` | 99 | `output_original_09.txt` |
| `input_original_10.csv` | 99 | `output_original_10.txt` |

## Usage

```
./area_and_topology_preserving_polygon_simplification <input_file> <target_vertices>
```

The program reads a CSV with columns `ring_id,vertex_id,x,y` and writes simplified output to stdout.
