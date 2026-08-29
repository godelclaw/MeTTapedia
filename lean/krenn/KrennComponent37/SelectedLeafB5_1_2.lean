import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_1_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6cc783db13d12da2b384684ee856d6498037d586c15b2c16901c0fb3352426e0"
def certificateSHA256 : String := "1cb86c66fcb88a2c09efa419e42a97ec711b9e96facde37d2db8fdcfe519434a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 54 → Fin 667 := ![
  7,
  14,
  27,
  167,
  168,
  171,
  175,
  176,
  180,
  182,
  183,
  256,
  260,
  280,
  294,
  295,
  296,
  297,
  298,
  299,
  307,
  310,
  313,
  315,
  316,
  317,
  342,
  343,
  393,
  410,
  411,
  424,
  430,
  433,
  446,
  450,
  466,
  474,
  482,
  483,
  523,
  542,
  587,
  604,
  605,
  646,
  656,
  657,
  658,
  659,
  660,
  662,
  663,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 54 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 54 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (10, 1), (33, 1), (49, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (36, 1), (42, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (33, 1), (49, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (36, 1), (42, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (33, 1), (49, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (51, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (36, 1), (39, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (28, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (39, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (36, 1), (39, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(28, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (33, 1), (49, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (36, 1), (42, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (33, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (21, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (28, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (28, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (36, 1), (39, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (36, 1), (39, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (36, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (36, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (36, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (27, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (36, 1), (39, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (8, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (25, 1), (44, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (25, 1), (44, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (27, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (27, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (20, 1), (28, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (25, 1), (28, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (27, 1), (33, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (27, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }]
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
    ¬ ∀ index : Fin 54,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_1_2.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_1_2
