import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB0_3_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "26513a3277297507d2a577acd03b1638a3df0222361f51e02cc355956598743b"
def certificateSHA256 : String := "6f1e907538ac7600f584fa5838730d04cf4c907144f42e3836a3b2e81e74d422"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 668 := ![
  1,
  6,
  10,
  11,
  149,
  151,
  153,
  168,
  177,
  195,
  257,
  300,
  312,
  319,
  363,
  435,
  450,
  461,
  605,
  609,
  643,
  654,
  655,
  656,
  657,
  658,
  661,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (19, 1), (21, 1), (45, 2), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (31, 1), (37, 1), (45, 2), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (45, 1), (47, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1), (45, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (45, 2), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (45, 2), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (45, 1), (47, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (45, 1), (47, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (31, 1), (41, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (34, 1), (41, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (34, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (34, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (34, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (35, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (35, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (23, 1), (31, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (23, 1), (34, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (21, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (31, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (34, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (31, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (34, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (34, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (19, 1), (21, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (31, 1), (37, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (47, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (41, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (41, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (31, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (34, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (34, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (21, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (35, 1), (41, 1), (45, 1), (54, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (34, 1), (35, 1), (41, 1), (45, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (23, 1), (31, 1), (41, 1), (45, 1), (54, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (23, 1), (34, 1), (41, 1), (45, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (35, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (45, 2), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (45, 2), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (45, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (45, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (21, 1), (23, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (21, 1), (45, 2), (50, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (21, 1), (45, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (31, 1), (37, 1), (45, 2), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (31, 1), (37, 1), (45, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (41, 1), (52, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (45, 1), (47, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (47, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (45, 1), (47, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1), (47, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (38, 1), (41, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (38, 1), (41, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (38, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (31, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (34, 1), (35, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (31, 1), (41, 2), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (34, 1), (41, 2), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (21, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (41, 1), (45, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (45, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (32, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (23, 1), (31, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (23, 1), (34, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (32, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (41, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (41, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (31, 1), (41, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (34, 1), (41, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (31, 1), (41, 1), (48, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (34, 1), (41, 1), (48, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (31, 1), (41, 1), (47, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (34, 1), (41, 1), (47, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (34, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (34, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (34, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (48, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (31, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (34, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (34, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (34, 1), (48, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (21, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (31, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (34, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (34, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (34, 1), (47, 1), (50, 1), (56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB0_3_6_4.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB0_3_6_4
