import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0a6bad87aa373b6153b84ae6136f57c47fe7d197a9d1357cd71acab10a9d1e58"
def certificateSHA256 : String := "119e0b797610703e4c91d5a5a24d81b8fe2a410f84ef7122599c0b275641130f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 41 → Fin 667 := ![
  6,
  7,
  11,
  13,
  16,
  18,
  21,
  23,
  135,
  137,
  139,
  158,
  159,
  160,
  186,
  191,
  207,
  245,
  302,
  309,
  362,
  364,
  373,
  374,
  443,
  453,
  454,
  557,
  579,
  587,
  604,
  605,
  619,
  656,
  657,
  659,
  660,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 41 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 41 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (50, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (50, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (43, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (39, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (32, 1), (35, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (50, 2), (59, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (26, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (38, 1), (45, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (26, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (21, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (29, 1), (43, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (21, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (26, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (29, 1), (43, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (7, 1), (21, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (26, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (29, 1), (43, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (46, 1), (50, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (21, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (29, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (16, 1), (21, 1), (24, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (16, 1), (24, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (16, 1), (24, 1), (29, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (18, 1), (21, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (18, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (18, 1), (29, 1), (43, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (16, 1), (21, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (16, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (16, 1), (29, 1), (43, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (46, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (43, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (21, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (29, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (32, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(26, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (38, 1), (46, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (32, 1), (46, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (32, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (7, 1), (21, 1), (22, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (22, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (22, 1), (29, 1), (43, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (7, 1), (21, 1), (22, 1), (24, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (22, 1), (24, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (22, 1), (24, 1), (29, 1), (43, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (21, 1), (22, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (29, 1), (43, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (21, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (29, 1), (43, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (58, 1)] }, { coefficient := -1, powers := [(38, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (21, 1), (36, 1), (58, 2), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (21, 1), (45, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (36, 1), (58, 2), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (45, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (29, 1), (36, 1), (43, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (29, 1), (43, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (38, 1), (46, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (46, 1), (50, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (21, 1), (45, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (26, 1), (45, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (29, 1), (43, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (30, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (26, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (29, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (21, 1), (22, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (22, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (22, 1), (29, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (38, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (27, 1), (32, 1), (46, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (22, 1), (32, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (35, 1)] }]
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
    ¬ ∀ index : Fin 41,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_7_1.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_7_1
