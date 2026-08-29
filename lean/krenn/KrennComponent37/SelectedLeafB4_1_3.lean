import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7891b0f817948f003e8350cb2950b7483746b50811432514c8efe361ac15b0b1"
def certificateSHA256 : String := "91b6e45f83cdac3c0abf93b131ea41b2876289b666fd33ad42f2a407e0090ef3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 667 := ![
  7,
  9,
  14,
  23,
  27,
  154,
  155,
  175,
  180,
  182,
  280,
  283,
  294,
  295,
  296,
  298,
  299,
  307,
  359,
  381,
  433,
  446,
  482,
  546,
  556,
  589,
  604,
  605,
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
def selectedEquations : Fin 36 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(10, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(15, 1), (24, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (15, 1), (24, 1), (32, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(10, 1), (15, 1), (24, 1), (32, 1), (38, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (15, 1), (24, 1), (32, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(10, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 2), (24, 1), (32, 1), (38, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 2), (32, 1), (36, 1), (38, 1), (39, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (15, 1), (24, 1), (32, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 2), (24, 1), (32, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 2), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (44, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (44, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (44, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (44, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (44, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (15, 1), (18, 1), (24, 1), (32, 1), (38, 1), (44, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (15, 1), (18, 1), (32, 1), (36, 1), (38, 1), (39, 1), (44, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 2), (24, 1), (32, 1), (38, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 2), (32, 1), (36, 1), (38, 1), (39, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (16, 1), (24, 1), (32, 1), (38, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (16, 1), (32, 1), (36, 1), (38, 1), (39, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (18, 1), (24, 1), (32, 1), (38, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (18, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(10, 1), (46, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (47, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (24, 1), (32, 1), (38, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (32, 1), (38, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (32, 1), (38, 1), (49, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (18, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(10, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (30, 1), (32, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (15, 1), (18, 1), (24, 1), (32, 1), (38, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (15, 1), (18, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 2), (24, 1), (32, 1), (38, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 2), (32, 1), (36, 1), (38, 1), (39, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (18, 1), (24, 1), (32, 1), (38, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (30, 1), (32, 1), (38, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (18, 1), (30, 1), (32, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (18, 1), (30, 1), (32, 1), (38, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (15, 1), (24, 1), (32, 2), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (32, 2), (36, 1), (38, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (30, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (18, 1), (30, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (15, 1), (24, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 2), (24, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 2), (32, 1), (36, 1), (38, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (24, 1), (32, 1), (38, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (27, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (27, 1), (32, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 2), (24, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 2), (32, 1), (36, 1), (38, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (18, 1), (24, 1), (32, 1), (38, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (30, 1), (32, 1), (38, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (30, 1), (32, 1), (38, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (38, 2), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (46, 1), (47, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (32, 1), (36, 1), (38, 2), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (46, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (24, 1), (32, 1), (38, 1), (47, 1), (53, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (32, 1), (36, 1), (38, 1), (39, 1), (47, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (46, 1), (58, 2), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (15, 1), (24, 1), (32, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (18, 1), (24, 1), (32, 1), (38, 1), (53, 1), (58, 2), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (18, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (15, 1), (24, 1), (32, 1), (35, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (15, 1), (32, 1), (35, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 2), (24, 1), (27, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 2), (27, 1), (32, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (32, 1), (38, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (32, 1), (38, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (15, 1), (24, 1), (32, 2), (38, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (15, 1), (32, 2), (36, 1), (38, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (18, 1), (24, 1), (32, 2), (38, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (18, 1), (32, 2), (36, 1), (38, 1), (39, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (15, 1), (22, 1), (24, 1), (32, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (15, 1), (22, 1), (32, 1), (36, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 2), (22, 1), (24, 1), (32, 1), (38, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 2), (22, 1), (32, 1), (36, 1), (38, 1), (39, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_1_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_1_3
