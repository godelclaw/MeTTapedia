import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "85fb8deafa648e97b2ff0748fd2cb6d0ede05236a6bff446abc1f77429a51f9c"
def certificateSHA256 : String := "3130b1de37b64c8fd5a6ef58ae10d40515a8e882e59b1e1ee6dc7e30099a20b8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 55 → Fin 667 := ![
  7,
  14,
  27,
  168,
  175,
  176,
  179,
  180,
  182,
  184,
  256,
  280,
  294,
  296,
  297,
  298,
  299,
  307,
  310,
  315,
  316,
  393,
  410,
  411,
  425,
  426,
  433,
  435,
  438,
  446,
  450,
  453,
  455,
  465,
  478,
  487,
  523,
  542,
  580,
  581,
  604,
  605,
  606,
  607,
  645,
  648,
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
def selectedEquations : Fin 55 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 55 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (10, 1), (36, 1), (42, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (36, 1), (42, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (51, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (28, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (28, 1), (49, 1), (51, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (28, 1), (49, 1), (52, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (28, 1), (49, 1), (52, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (30, 1), (49, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (25, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (36, 1), (42, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (25, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (28, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (26, 1), (28, 1), (49, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (30, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (26, 1), (28, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (39, 1), (52, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (28, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (28, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (51, 1), (52, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (28, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (30, 1), (49, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (20, 1), (25, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (52, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (39, 1), (51, 1), (52, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (27, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (25, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (26, 1), (28, 1), (49, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (30, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (25, 1), (38, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (25, 1), (46, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (25, 1), (38, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (25, 1), (46, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (25, 1), (49, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 2), (20, 1), (25, 1), (49, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (25, 1), (30, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (25, 1), (39, 1), (51, 1), (52, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (27, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (39, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (27, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (20, 1), (26, 1), (28, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (25, 1), (26, 1), (28, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (23, 1), (25, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (25, 1), (28, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (25, 1), (30, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (39, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (32, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (27, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }]
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
    ¬ ∀ index : Fin 55,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_1_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_1_4
