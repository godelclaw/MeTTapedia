import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a5207edea4d70bce558ce8d38af7dc26e913d450d2b1b81efe8d7c669519b40c"
def certificateSHA256 : String := "6ba2f2bd8bb6745d86baee3006ce61fa9fbc722267cee5bbd929b3e6a4d8ba2b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 667 := ![
  9,
  14,
  16,
  19,
  23,
  71,
  79,
  149,
  151,
  152,
  153,
  171,
  179,
  180,
  181,
  221,
  283,
  298,
  299,
  303,
  307,
  311,
  312,
  433,
  438,
  446,
  450,
  556,
  566,
  570,
  583,
  584,
  589,
  604,
  605,
  650,
  656,
  657,
  659,
  660,
  661,
  662,
  663,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(7, 1), (24, 1), (26, 1), (44, 1), (52, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 4, powers := [(10, 1), (24, 1), (26, 1), (44, 1), (46, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(10, 1), (24, 1), (26, 1), (44, 1), (52, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(15, 1), (24, 1), (26, 1), (44, 1), (52, 2), (58, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(10, 1), (24, 1), (26, 1), (44, 1), (52, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(15, 1), (24, 1), (26, 1), (44, 1), (52, 1), (53, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (44, 1), (52, 1), (53, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (44, 2), (55, 1), (57, 1), (63, 1), (65, 1)] }, { coefficient := 2, powers := [(24, 1), (26, 1), (44, 1), (53, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (44, 1), (49, 1), (51, 1), (57, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (44, 1), (49, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (39, 1), (44, 1), (53, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (26, 1), (30, 1), (44, 1), (53, 1), (57, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 2), (44, 1), (53, 1), (57, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (44, 1), (53, 1), (54, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (44, 1), (55, 1), (57, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (33, 1), (39, 1), (44, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (12, 1), (24, 1), (26, 1), (44, 2), (52, 1), (58, 1), (60, 1), (65, 2)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (24, 1), (26, 1), (44, 2), (46, 1), (52, 1), (58, 1), (65, 2)] }, { coefficient := -2, powers := [(12, 1), (15, 1), (24, 1), (26, 1), (44, 2), (52, 2), (58, 1), (65, 2)] }, { coefficient := -2, powers := [(12, 1), (16, 1), (24, 1), (26, 1), (44, 1), (46, 1), (52, 1), (58, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(44, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (26, 1), (44, 1), (49, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (46, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (26, 1), (44, 1), (46, 1), (49, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1), (63, 1), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 2), (44, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (44, 1), (49, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (44, 1), (55, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (44, 2), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1), (47, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(63, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (12, 1), (24, 1), (26, 1), (44, 1), (52, 1), (58, 1), (60, 1), (65, 2)] }, { coefficient := -2, powers := [(10, 1), (12, 1), (24, 1), (26, 1), (44, 1), (46, 1), (52, 1), (58, 1), (65, 2)] }, { coefficient := 2, powers := [(12, 1), (15, 1), (24, 1), (26, 1), (44, 1), (52, 2), (58, 1), (65, 2)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (52, 2), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (46, 1), (52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (30, 1), (44, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (44, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (26, 1), (44, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (44, 2), (48, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (55, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (49, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (30, 1), (44, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(10, 1), (24, 1), (26, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(15, 1), (24, 1), (26, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (44, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (44, 1), (48, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (46, 1), (52, 1), (58, 1), (65, 2)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (27, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (15, 1), (24, 1), (26, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (38, 1), (44, 1), (52, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (46, 1), (47, 1), (52, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (46, 1), (52, 2), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (39, 1), (44, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (48, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (49, 1), (55, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (18, 1), (24, 1), (26, 1), (32, 1), (44, 1), (52, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(12, 1), (26, 1), (30, 1), (44, 1), (46, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (44, 2), (55, 1), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (30, 1), (44, 1), (49, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (30, 1), (44, 1), (49, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (36, 1), (39, 1), (44, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (26, 1), (30, 1), (44, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 2), (44, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (44, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (44, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (33, 1), (39, 1), (44, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(1, 1), (12, 1), (24, 1), (26, 1), (44, 1), (46, 1), (52, 1), (58, 2), (65, 2)] }, { coefficient := -2, powers := [(1, 1), (12, 1), (24, 1), (26, 1), (44, 1), (52, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (24, 1), (26, 1), (35, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(12, 1), (15, 1), (24, 1), (26, 1), (27, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (26, 1), (36, 1), (44, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (44, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (12, 1), (24, 1), (26, 1), (32, 1), (44, 1), (46, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (22, 1), (24, 1), (26, 1), (44, 1), (52, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(12, 1), (15, 1), (22, 1), (24, 1), (26, 1), (44, 1), (52, 2), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(40, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_4_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_4_3
