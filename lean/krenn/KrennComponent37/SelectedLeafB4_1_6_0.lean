import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_1_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "265923a13f0706c073446515ac0fd908f6fe27a5863c8995427bc06ed30db01e"
def certificateSHA256 : String := "078e44954221f7ebbd03399a7eb9d4f133724b723009dbb4076544ca35172abc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 670 := ![
  7,
  52,
  171,
  179,
  180,
  181,
  294,
  295,
  298,
  299,
  313,
  317,
  381,
  410,
  411,
  424,
  433,
  438,
  447,
  450,
  454,
  474,
  505,
  523,
  566,
  605,
  638,
  639,
  656,
  657,
  659,
  660,
  662,
  664,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (36, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (36, 1), (46, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (55, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (26, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (24, 1), (26, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (26, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (32, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (32, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (32, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (51, 1), (52, 2), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (28, 1), (42, 1), (52, 2), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (23, 1), (51, 1), (52, 2), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (37, 1), (52, 2), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (29, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (28, 1), (42, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (23, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (22, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (29, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (44, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (44, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (26, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (24, 1), (26, 1), (32, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (24, 1), (32, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (26, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (51, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (32, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (49, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (24, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (19, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (19, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (12, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (39, 1), (52, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (42, 1), (52, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (49, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (32, 1), (39, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (32, 1), (42, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (42, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (32, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (32, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (24, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (22, 1), (33, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (32, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (33, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (32, 1), (33, 1), (38, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (24, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (24, 1), (26, 1), (32, 1), (47, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (47, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (24, 1), (26, 1), (32, 1), (41, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (24, 1), (32, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (24, 1), (26, 1), (47, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (24, 1), (41, 1), (44, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (24, 1), (44, 1), (46, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (24, 1), (47, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (24, 1), (26, 1), (32, 1), (46, 1), (47, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (24, 1), (32, 1), (46, 1), (47, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (19, 1), (22, 1), (24, 1), (26, 1), (41, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (19, 1), (22, 1), (24, 1), (41, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (19, 1), (24, 1), (26, 1), (32, 1), (41, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (19, 1), (24, 1), (32, 1), (41, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (24, 1), (41, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (24, 1), (44, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (24, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (24, 1), (41, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (23, 1), (49, 1), (51, 1), (52, 2), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (41, 1), (44, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (44, 1), (51, 1), (52, 2), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (28, 1), (42, 1), (44, 1), (52, 2), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (29, 1), (42, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (37, 1), (49, 1), (52, 2), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (22, 1), (29, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (24, 1), (41, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (29, 1), (41, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (24, 1), (26, 1), (32, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (24, 1), (32, 1), (38, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (24, 1), (26, 1), (32, 1), (38, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (24, 1), (32, 1), (38, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1)] }, { coefficient := -1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (32, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (32, 1), (48, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (22, 1), (52, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (32, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (32, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (44, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (12, 1), (32, 1), (44, 1), (46, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (32, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (49, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (32, 1), (46, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (19, 1), (22, 1), (48, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (19, 1), (32, 1), (46, 1), (48, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (44, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (22, 1), (48, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (32, 1), (38, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (32, 1), (38, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (32, 1), (38, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_1_6_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_1_6_0
