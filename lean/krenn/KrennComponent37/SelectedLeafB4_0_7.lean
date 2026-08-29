import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_0_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e1b2935512e0370420dc6af18d165c5593a4da054e1045b5c162bb8fdd4b68c6"
def certificateSHA256 : String := "d7dd154e3161eefb0b6c3698ff51f39f1518c2a212dc3671efa1b79ccfe28c99"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 67 → Fin 667 := ![
  9,
  14,
  23,
  168,
  175,
  176,
  178,
  179,
  180,
  181,
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
  311,
  312,
  356,
  364,
  369,
  393,
  395,
  410,
  411,
  414,
  425,
  430,
  432,
  433,
  435,
  436,
  438,
  445,
  446,
  449,
  450,
  453,
  482,
  487,
  526,
  555,
  556,
  566,
  567,
  580,
  589,
  594,
  596,
  604,
  605,
  619,
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
def selectedEquations : Fin 67 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
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
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 67 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (24, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(10, 1), (30, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (24, 1), (44, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (30, 1), (44, 1), (49, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (24, 1), (44, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (30, 1), (44, 1), (46, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (24, 1), (44, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (30, 1), (44, 1), (49, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (24, 1), (44, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (30, 1), (44, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (24, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (30, 1), (46, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (24, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (30, 1), (49, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (49, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(29, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (55, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1), (48, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (53, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (24, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (49, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (24, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (30, 1), (46, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (24, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (30, 1), (49, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (30, 1), (49, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (53, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (58, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (49, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (48, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (21, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (25, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (23, 1), (48, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (26, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (25, 1), (48, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(21, 1), (58, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(28, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (21, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(6, 1), (23, 1), (25, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (28, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (48, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (46, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (27, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (15, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (47, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (46, 1), (47, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (47, 1), (53, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (47, 1), (49, 1), (53, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (46, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (48, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (46, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(6, 1), (21, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (46, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(6, 1), (25, 1), (48, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (26, 1), (46, 1), (48, 1), (61, 1)] }, { coefficient := 2, powers := [(6, 1), (37, 1), (48, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 3, powers := [(6, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(48, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (28, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (24, 1), (46, 1), (58, 2), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (24, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (30, 1), (46, 1), (49, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (30, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (24, 1), (53, 1), (58, 2), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (30, 1), (49, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (24, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (27, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (25, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (24, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (30, 1), (32, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (24, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (24, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (51, 1), (58, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 67,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_0_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_0_7
