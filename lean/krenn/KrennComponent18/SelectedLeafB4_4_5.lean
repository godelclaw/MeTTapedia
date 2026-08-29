import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9bed09b40b9eac5c6b1e416192e26a24cee7754725859bafbd6f39b25a59a500"
def certificateSHA256 : String := "c6f15a66ac1e7d3e5883b776a6264e887a85ed87001fa3851037d8fe0f27da01"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 667 := ![
  2,
  10,
  11,
  17,
  19,
  23,
  24,
  145,
  148,
  149,
  150,
  166,
  167,
  301,
  318,
  387,
  409,
  433,
  437,
  439,
  443,
  506,
  551,
  606,
  656,
  657,
  659,
  660,
  662,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (24, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (26, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (31, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (37, 1), (40, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (31, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (37, 1), (40, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (36, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (37, 1), (40, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (31, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (31, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (33, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (36, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (37, 1), (40, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (33, 1), (39, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (37, 1), (39, 1), (40, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (22, 1), (24, 1), (25, 1), (47, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (24, 1), (45, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(4, 1), (24, 1), (25, 1), (28, 1), (47, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(4, 1), (24, 1), (25, 1), (36, 1), (47, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (28, 1), (45, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (36, 1), (45, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(7, 1), (24, 1), (25, 1), (33, 1), (46, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (33, 1), (45, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(15, 1), (24, 1), (25, 1), (33, 1), (39, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (33, 1), (39, 1), (45, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (28, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (33, 1), (39, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (28, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (46, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (47, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (46, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (47, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (22, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (24, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (24, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(7, 1), (24, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(15, 1), (24, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (49, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (18, 1), (22, 1), (24, 1), (25, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (18, 1), (24, 1), (25, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (18, 1), (24, 1), (25, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (22, 1), (29, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (28, 1), (29, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (29, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (18, 1), (24, 1), (25, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1)] }, { coefficient := 2, powers := [(15, 1), (18, 1), (24, 1), (25, 1), (33, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (25, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (26, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (28, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (36, 1), (39, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (28, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (28, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (22, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (28, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (28, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (33, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (28, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (13, 1), (22, 1), (31, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (22, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (28, 1), (31, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (28, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (31, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (36, 1), (37, 1), (40, 1), (52, 1)] }, { coefficient := 2, powers := [(4, 1), (17, 1), (22, 1), (24, 1), (25, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (22, 1), (24, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (17, 1), (24, 1), (25, 1), (28, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (17, 1), (24, 1), (25, 1), (36, 1), (47, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (24, 1), (28, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (24, 1), (36, 1), (45, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (22, 1), (31, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (28, 1), (31, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (33, 1), (37, 1), (40, 1), (46, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (24, 1), (25, 1), (33, 1), (46, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (24, 1), (33, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (31, 1), (33, 1), (39, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (33, 1), (37, 1), (39, 1), (40, 1)] }, { coefficient := -2, powers := [(15, 1), (17, 1), (24, 1), (25, 1), (33, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (24, 1), (33, 1), (39, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_4_5.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_4_5
