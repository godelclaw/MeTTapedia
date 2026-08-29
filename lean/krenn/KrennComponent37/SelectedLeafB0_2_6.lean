import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6acbac7220baa7ed7d464974726e20bce86857561fe872112a311b26346ba04b"
def certificateSHA256 : String := "c30de9aac52d36fa52c8c23bdb00f3acbeaff7325f4f8f29a4b644d4f4803758"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 667 := ![
  5,
  52,
  167,
  168,
  175,
  179,
  180,
  256,
  260,
  279,
  297,
  298,
  299,
  316,
  342,
  438,
  445,
  449,
  450,
  453,
  454,
  472,
  479,
  487,
  495,
  498,
  523,
  566,
  580,
  604,
  605,
  608,
  621,
  623,
  624,
  626,
  642,
  645,
  656,
  657,
  658,
  659,
  660,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (28, 1), (46, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (30, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (28, 1), (41, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (30, 1), (41, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (36, 1), (41, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (41, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (38, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (38, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (28, 1), (41, 1), (46, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (28, 1), (46, 2), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (28, 1), (46, 1), (52, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (30, 1), (41, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (30, 1), (46, 2), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (30, 1), (46, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (36, 1), (41, 1), (46, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (36, 1), (46, 2), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (36, 1), (46, 1), (52, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (41, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (46, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (52, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (41, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (41, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (46, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (52, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (28, 1), (46, 2), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (30, 1), (46, 2), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (36, 1), (46, 2), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(23, 1), (44, 1), (46, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (46, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (41, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (27, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (27, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (27, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (27, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (21, 1), (27, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (21, 1), (27, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (21, 1), (27, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (22, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (27, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (27, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (21, 1), (22, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (21, 1), (22, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (21, 1), (22, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (27, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (27, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (27, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (22, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (27, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (27, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (28, 1), (32, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (30, 1), (32, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (32, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (32, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (28, 1), (32, 1), (38, 1), (46, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (28, 1), (32, 1), (41, 1), (46, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (28, 1), (32, 1), (46, 2), (52, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (30, 1), (32, 1), (38, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (30, 1), (32, 1), (41, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (30, 1), (32, 1), (46, 2), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (32, 1), (36, 1), (38, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (32, 1), (36, 1), (41, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (32, 1), (36, 1), (46, 2), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (28, 1), (38, 1), (46, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (28, 1), (41, 1), (46, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (28, 1), (46, 2), (52, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (30, 1), (38, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (30, 1), (41, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (30, 1), (46, 2), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (36, 1), (38, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (36, 1), (41, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (27, 1), (36, 1), (46, 2), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (27, 1), (28, 1), (46, 1), (48, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (27, 1), (30, 1), (46, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (27, 1), (36, 1), (46, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (32, 1), (38, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (32, 1), (41, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (32, 1), (46, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (28, 1), (38, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (28, 1), (41, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (28, 1), (46, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (30, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (30, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (22, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (28, 1), (38, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (28, 1), (41, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (28, 1), (46, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (30, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (30, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (28, 1), (48, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (22, 1), (30, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (22, 1), (36, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (27, 1), (28, 1), (48, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (27, 1), (30, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (27, 1), (36, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (28, 1), (38, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (28, 1), (41, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (28, 1), (46, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (30, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (30, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (28, 1), (38, 1), (46, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (28, 1), (41, 1), (46, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (28, 1), (46, 2), (52, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (30, 1), (38, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (30, 1), (41, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (30, 1), (46, 2), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (36, 1), (38, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (36, 1), (41, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (21, 1), (22, 1), (36, 1), (46, 2), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (28, 1), (46, 1), (48, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (30, 1), (46, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (36, 1), (46, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (33, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (41, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (44, 1), (46, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (47, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (38, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (41, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (46, 2), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (46, 2), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (46, 2), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(37, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (28, 1), (32, 1), (41, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (28, 1), (32, 1), (46, 2), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (15, 1), (28, 1), (32, 1), (46, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (30, 1), (32, 1), (41, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (30, 1), (32, 1), (46, 2), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (30, 1), (32, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (32, 1), (36, 1), (41, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (32, 1), (36, 1), (46, 2), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (32, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (32, 1), (41, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (32, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (32, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (28, 1), (32, 1), (46, 2), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (30, 1), (32, 1), (46, 2), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (32, 1), (36, 1), (46, 2), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (48, 1)] }]
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
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_2_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_2_6
