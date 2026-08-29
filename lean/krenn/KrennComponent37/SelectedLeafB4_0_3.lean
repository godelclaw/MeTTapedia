import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_0_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9821639b11662f7d5672ddb2a5e40c7e9670d9f0647068dc0689cb75c6b3caef"
def certificateSHA256 : String := "a40eca49ba0aa06137932372c517592a2d092fc7517eef8617c64333e6066809"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 667 := ![
  9,
  14,
  23,
  168,
  175,
  176,
  178,
  179,
  180,
  256,
  260,
  280,
  283,
  294,
  295,
  296,
  298,
  299,
  307,
  310,
  393,
  395,
  411,
  414,
  430,
  432,
  433,
  436,
  438,
  445,
  446,
  450,
  453,
  482,
  555,
  556,
  567,
  589,
  604,
  605,
  650,
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
def selectedEquations : Fin 50 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (29, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (49, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (39, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(10, 1), (21, 1), (29, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (29, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(10, 1), (24, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(10, 1), (30, 1), (46, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (49, 1), (57, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(10, 1), (36, 1), (39, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (39, 1), (57, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (29, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (49, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (39, 1), (52, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (49, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (39, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (49, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (39, 1), (53, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (29, 1), (44, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (24, 1), (44, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (30, 1), (44, 1), (49, 1), (58, 1), (60, 1), (64, 2)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (36, 1), (39, 1), (44, 1), (58, 1), (60, 1), (64, 2)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (21, 1), (29, 1), (44, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (24, 1), (44, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (30, 1), (44, 1), (46, 1), (49, 1), (58, 1), (64, 2)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (36, 1), (39, 1), (44, 1), (46, 1), (58, 1), (64, 2)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (21, 1), (29, 1), (44, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (24, 1), (44, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (30, 1), (44, 1), (49, 1), (53, 1), (58, 1), (64, 2)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (36, 1), (39, 1), (44, 1), (53, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (21, 1), (29, 1), (44, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (24, 1), (44, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (30, 1), (44, 1), (49, 1), (52, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (36, 1), (39, 1), (44, 1), (52, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(12, 1), (16, 1), (21, 1), (29, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (24, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (30, 1), (46, 1), (49, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(12, 1), (16, 1), (36, 1), (39, 1), (46, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (21, 1), (29, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (24, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (30, 1), (49, 1), (53, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (36, 1), (39, 1), (53, 1), (58, 1), (64, 2)] }],
  [{ coefficient := -1, powers := [(24, 1), (47, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (55, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (49, 1), (51, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(29, 1), (49, 1), (55, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (51, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (44, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (47, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (55, 1), (58, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1), (48, 1), (58, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (29, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (49, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (29, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (24, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (49, 1), (58, 1), (60, 1), (64, 2)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (36, 1), (39, 1), (58, 1), (60, 1), (64, 2)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (21, 1), (29, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (24, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (30, 1), (46, 1), (49, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (36, 1), (39, 1), (46, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (21, 1), (29, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (24, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (30, 1), (49, 1), (53, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (36, 1), (39, 1), (53, 1), (58, 1), (64, 2)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (21, 1), (29, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (30, 1), (49, 1), (52, 1), (58, 1), (64, 2)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (36, 1), (39, 1), (52, 1), (58, 1), (64, 2)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (58, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (53, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (58, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (29, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (52, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (29, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (46, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (46, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (29, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (39, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (48, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (33, 1), (39, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (58, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(21, 1), (58, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (39, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (39, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (29, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (46, 1), (49, 1), (58, 1), (64, 2)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (46, 1), (58, 1), (64, 2)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (29, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (53, 1), (58, 1), (64, 2)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (53, 1), (58, 1), (64, 2)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (27, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (27, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (30, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (36, 1), (39, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (21, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (30, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (36, 1), (39, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (44, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (29, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (29, 1), (46, 1), (47, 1), (54, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (29, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (47, 1), (54, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (38, 1), (49, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (46, 1), (47, 1), (49, 1), (54, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (46, 1), (49, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (38, 1), (39, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (46, 1), (47, 1), (54, 1), (58, 1), (64, 2)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (46, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (47, 1), (53, 1), (54, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (47, 1), (53, 1), (54, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (47, 1), (49, 1), (53, 1), (54, 1), (58, 1), (64, 2)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (47, 1), (53, 1), (54, 1), (58, 1), (64, 2)] }],
  [{ coefficient := -1, powers := [(20, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (58, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(48, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (21, 1), (29, 1), (46, 1), (58, 2), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (21, 1), (29, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (24, 1), (46, 1), (58, 2), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (24, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (30, 1), (46, 1), (49, 1), (58, 2), (64, 2)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (30, 1), (49, 1), (57, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (36, 1), (39, 1), (46, 1), (58, 2), (64, 2)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (36, 1), (39, 1), (57, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (21, 1), (29, 1), (53, 1), (58, 2), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (24, 1), (53, 1), (58, 2), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (30, 1), (49, 1), (53, 1), (58, 2), (64, 2)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (36, 1), (39, 1), (53, 1), (58, 2), (64, 2)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (29, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (24, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (35, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (35, 1), (36, 1), (39, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (21, 1), (27, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (27, 1), (30, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (27, 1), (36, 1), (39, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 2), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (21, 1), (29, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (24, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (46, 1), (49, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (36, 1), (39, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (29, 1), (32, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (30, 1), (32, 1), (49, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (32, 1), (36, 1), (39, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (22, 1), (29, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (24, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (30, 1), (49, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (36, 1), (39, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (21, 1), (22, 1), (29, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (24, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (30, 1), (49, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (36, 1), (39, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_0_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_0_3
