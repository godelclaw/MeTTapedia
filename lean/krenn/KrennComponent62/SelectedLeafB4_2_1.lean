import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2aefbc7076bb36eeac8255fa0df36a8f8ab2c4e6dcb83c048b63c4b434ceb08d"
def certificateSHA256 : String := "69ca01afb878f490f0572e543a417cec2319cad0993b66c1cc54b0f8de011c3c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 51 → Fin 667 := ![
  7,
  11,
  18,
  21,
  22,
  23,
  139,
  142,
  147,
  153,
  207,
  223,
  252,
  293,
  294,
  295,
  296,
  301,
  302,
  309,
  313,
  362,
  374,
  390,
  435,
  437,
  438,
  441,
  444,
  454,
  464,
  465,
  476,
  483,
  491,
  496,
  497,
  557,
  579,
  604,
  605,
  609,
  656,
  657,
  658,
  659,
  660,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 51 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (41, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 51 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (26, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (26, 1), (36, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (21, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (29, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (26, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := 2, powers := [(17, 1), (21, 1), (36, 1), (58, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (36, 1), (43, 1)] }, { coefficient := 2, powers := [(17, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (43, 2), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (26, 1), (38, 1), (43, 1), (62, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1), (43, 1), (62, 1)] }, { coefficient := -2, powers := [(24, 1), (32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (12, 1), (26, 1), (43, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (12, 1), (26, 1), (43, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (26, 1), (43, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (12, 1), (26, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (12, 1), (32, 1), (50, 1), (52, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (21, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (29, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (32, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (17, 1), (26, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (17, 1), (26, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (17, 1), (26, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (17, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (26, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (32, 1), (35, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (14, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (32, 1), (46, 1)] }],
  [{ coefficient := -4, powers := [(5, 1), (14, 1), (32, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (26, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (38, 1), (43, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (22, 1), (32, 1), (35, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (26, 1), (27, 1), (43, 1), (46, 1), (48, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (26, 1), (27, 1), (43, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (27, 1), (43, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (27, 1), (43, 1), (46, 1), (48, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (27, 1), (43, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (26, 1), (27, 1), (46, 1), (48, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (26, 1), (27, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (27, 1), (32, 1), (46, 1), (48, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (27, 1), (32, 1), (46, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (27, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (27, 1), (29, 1), (43, 1), (46, 1), (51, 1)] }, { coefficient := 2, powers := [(7, 1), (27, 1), (32, 1), (38, 1), (46, 1), (51, 1)] }, { coefficient := 2, powers := [(14, 1), (22, 1), (32, 1), (35, 1), (41, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(14, 1), (22, 1), (32, 1), (35, 1), (51, 1), (56, 1)] }, { coefficient := -2, powers := [(14, 1), (27, 1), (32, 1), (35, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (43, 2), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (38, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(26, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (26, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (27, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (27, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(7, 1), (27, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := -2, powers := [(14, 1), (22, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := -2, powers := [(14, 1), (27, 1), (32, 1), (35, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (26, 1), (27, 1), (43, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (27, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (27, 1), (29, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(7, 1), (27, 1), (32, 1), (38, 1), (51, 1)] }, { coefficient := 2, powers := [(14, 1), (27, 1), (32, 1), (35, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (16, 1), (22, 1), (32, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (38, 1), (43, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (16, 1), (26, 1), (27, 1), (43, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (16, 1), (21, 1), (27, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (16, 1), (27, 1), (29, 1), (43, 1), (51, 1)] }, { coefficient := 2, powers := [(7, 1), (16, 1), (27, 1), (32, 1), (38, 1), (51, 1)] }, { coefficient := -2, powers := [(14, 1), (16, 1), (27, 1), (32, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (16, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (16, 1), (26, 1), (27, 1), (46, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (16, 1), (27, 1), (32, 1), (46, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (16, 1), (22, 1), (32, 1), (35, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (43, 1), (53, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (32, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (26, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (26, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (32, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (23, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (23, 1), (26, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (23, 1), (27, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (23, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (27, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (27, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 2, powers := [(14, 1), (22, 1), (23, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := 2, powers := [(14, 1), (23, 1), (27, 1), (32, 1), (35, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (24, 1), (26, 1), (43, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (21, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (26, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (29, 1), (43, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -2, powers := [(8, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (26, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (27, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (27, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(7, 1), (27, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 2, powers := [(14, 1), (22, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := 2, powers := [(14, 1), (27, 1), (32, 1), (35, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (38, 1), (43, 1), (52, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (26, 1), (41, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (26, 1), (41, 1), (43, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (27, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (27, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (27, 1), (29, 1), (43, 1)] }, { coefficient := 2, powers := [(7, 1), (27, 1), (32, 1), (38, 1)] }, { coefficient := -2, powers := [(14, 1), (27, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (22, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (17, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (17, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (17, 1), (26, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (17, 1), (32, 1), (50, 1)] }, { coefficient := -2, powers := [(14, 1), (17, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (26, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (38, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (43, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (16, 1), (22, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (16, 1), (26, 1), (27, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (16, 1), (21, 1), (27, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (16, 1), (27, 1), (29, 1), (43, 1)] }, { coefficient := -2, powers := [(7, 1), (16, 1), (27, 1), (32, 1), (38, 1)] }, { coefficient := 2, powers := [(14, 1), (16, 1), (27, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (38, 1), (43, 1), (44, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1), (38, 1), (43, 1), (44, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (12, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (12, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (14, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (12, 1), (26, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (12, 1), (32, 1), (50, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (21, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (29, 1), (43, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (32, 1), (38, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (26, 1), (41, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (26, 1), (38, 1), (43, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (26, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := -2, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 2, powers := [(14, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (16, 1), (26, 1), (27, 1), (43, 1), (46, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (16, 1), (26, 1), (27, 1), (43, 1), (46, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (16, 1), (26, 1), (27, 1), (46, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (16, 1), (27, 1), (32, 1), (46, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(14, 1), (16, 1), (22, 1), (32, 1), (35, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(35, 1), (58, 1)] }, { coefficient := 2, powers := [(38, 1), (55, 1)] }, { coefficient := 2, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (26, 1), (36, 1), (43, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (26, 1), (39, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (36, 1), (43, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (39, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (36, 1), (43, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (39, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (26, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (26, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (32, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (32, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := -2, powers := [(14, 1), (32, 1), (35, 1), (36, 1), (59, 1)] }, { coefficient := -2, powers := [(14, 1), (32, 1), (35, 1), (39, 1), (56, 1)] }, { coefficient := -4, powers := [(14, 1), (32, 1), (35, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (26, 1), (38, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (26, 1), (38, 1), (41, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (26, 1), (38, 1), (41, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (8, 1), (26, 1), (33, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (26, 1), (33, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (16, 1), (26, 1), (27, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (14, 1), (26, 1), (33, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (26, 1), (33, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (32, 1), (33, 1), (50, 1)] }, { coefficient := 2, powers := [(7, 1), (8, 1), (26, 1), (33, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (8, 1), (32, 1), (33, 1), (50, 1)] }, { coefficient := 2, powers := [(7, 1), (16, 1), (21, 1), (27, 1), (41, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (16, 1), (27, 1), (29, 1), (41, 1), (43, 1)] }, { coefficient := 2, powers := [(7, 1), (16, 1), (27, 1), (32, 1), (38, 1), (41, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (32, 1), (33, 1), (35, 1)] }, { coefficient := -2, powers := [(14, 1), (16, 1), (27, 1), (32, 1), (35, 1), (41, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (27, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (12, 1), (18, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (12, 1), (23, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (12, 1), (18, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (12, 1), (23, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (14, 1), (18, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (14, 1), (23, 1), (26, 1), (27, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (12, 1), (18, 1), (26, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (12, 1), (18, 1), (27, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := 2, powers := [(4, 1), (12, 1), (23, 1), (26, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (12, 1), (23, 1), (27, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := 2, powers := [(4, 1), (29, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (18, 1), (21, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (18, 1), (27, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (18, 1), (27, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (21, 1), (23, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (23, 1), (27, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (23, 1), (27, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (18, 1), (22, 1), (26, 1), (41, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(10, 1), (21, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (18, 1), (22, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (18, 1), (27, 1), (32, 1), (35, 1), (46, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (22, 1), (23, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (23, 1), (27, 1), (32, 1), (35, 1), (46, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (24, 1), (26, 1), (41, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (26, 1), (43, 1)] }, { coefficient := -2, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (26, 1), (43, 2)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (26, 1), (38, 1), (43, 1)] }, { coefficient := -2, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := -2, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (26, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1), (43, 1), (61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 51,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_2_1.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_2_1
