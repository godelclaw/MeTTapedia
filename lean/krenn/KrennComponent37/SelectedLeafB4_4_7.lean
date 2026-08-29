import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "01be31c7674c3b79dc4c9e543fd9d6e31b0d6af1018b5be3cead641ea2c8676c"
def certificateSHA256 : String := "87addbfdbf79a45754048533cd54d0f14e1c85b5c66c5cb39edb40113a7935ba"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 667 := ![
  8,
  9,
  12,
  14,
  16,
  19,
  23,
  149,
  151,
  152,
  167,
  171,
  175,
  178,
  179,
  180,
  183,
  221,
  283,
  298,
  299,
  307,
  394,
  414,
  433,
  438,
  446,
  450,
  520,
  556,
  583,
  584,
  589,
  604,
  605,
  652,
  656,
  657,
  659,
  660,
  661,
  662,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (30, 1), (47, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (36, 1), (39, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := 2, powers := [(10, 1), (26, 1), (36, 1), (39, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (36, 1), (39, 1), (47, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (36, 1), (39, 1), (47, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (26, 1), (28, 1), (47, 1), (53, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1), (36, 1), (39, 1), (47, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (36, 1), (39, 1), (47, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (32, 1), (36, 1), (39, 1), (47, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (26, 1), (45, 1), (47, 1), (51, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (47, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (47, 1), (49, 1), (51, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (26, 1), (30, 1), (47, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 2), (47, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (47, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (33, 1), (39, 1), (47, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (26, 1), (36, 1), (39, 1), (44, 1), (47, 1), (60, 1), (66, 2)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (26, 1), (36, 1), (39, 1), (44, 1), (46, 1), (47, 1), (66, 2)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (26, 1), (36, 1), (39, 1), (44, 1), (47, 1), (52, 1), (66, 2)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (26, 1), (36, 1), (39, 1), (46, 1), (47, 1), (66, 2)] }],
  [{ coefficient := 1, powers := [(47, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (47, 1), (49, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (45, 1), (47, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 2), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (45, 1), (47, 1), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (47, 1), (55, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (47, 2), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (47, 1), (49, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (26, 1), (36, 1), (39, 1), (47, 1), (60, 1), (66, 2)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (26, 1), (36, 1), (39, 1), (46, 1), (47, 1), (66, 2)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (26, 1), (36, 1), (39, 1), (47, 1), (52, 1), (66, 2)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (36, 1), (39, 1), (47, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (36, 1), (39, 1), (46, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (26, 1), (32, 1), (36, 1), (39, 1), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (47, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (47, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (47, 1), (49, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (30, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (28, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (26, 1), (36, 1), (39, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (36, 1), (39, 1), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (36, 1), (39, 1), (46, 1), (47, 1), (66, 2)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (27, 1), (36, 1), (39, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (15, 1), (26, 1), (36, 1), (39, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (47, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (36, 1), (39, 1), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (36, 1), (38, 1), (39, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (36, 1), (39, 1), (46, 1), (47, 2), (54, 1), (66, 2)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (36, 1), (39, 1), (46, 1), (47, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (26, 1), (45, 1), (47, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (39, 1), (47, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (49, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (26, 1), (32, 1), (36, 1), (39, 1), (47, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (30, 1), (47, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (26, 1), (28, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (26, 1), (45, 1), (47, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (47, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (30, 1), (47, 1), (49, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (26, 1), (30, 1), (47, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 2), (47, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (47, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (33, 1), (39, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (12, 1), (26, 1), (36, 1), (39, 1), (46, 1), (47, 1), (58, 1), (66, 2)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (26, 1), (36, 1), (39, 1), (47, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (26, 1), (35, 1), (36, 1), (39, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (26, 1), (27, 1), (36, 1), (39, 1), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (47, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (47, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (36, 1), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (26, 1), (32, 1), (36, 1), (39, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (29, 1), (34, 1), (47, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (26, 1), (36, 1), (39, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (26, 1), (36, 1), (39, 1), (47, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(40, 1), (63, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_4_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_4_7
