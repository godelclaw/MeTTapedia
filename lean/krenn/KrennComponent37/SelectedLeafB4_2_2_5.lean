import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_2_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b0a65bc2e33546ccc286310a4500436f235ea2566102566947267c48cba0a8ae"
def certificateSHA256 : String := "656591079a0ab4f0d6a5a2bbbdc6a6635fe467fdddec14eb01ba46e171546ed7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 56 → Fin 670 := ![
  5,
  14,
  18,
  23,
  24,
  167,
  168,
  171,
  175,
  179,
  183,
  257,
  279,
  280,
  294,
  295,
  296,
  297,
  298,
  299,
  307,
  310,
  312,
  315,
  316,
  349,
  369,
  370,
  411,
  435,
  437,
  438,
  445,
  446,
  449,
  450,
  453,
  454,
  476,
  478,
  479,
  482,
  487,
  519,
  566,
  581,
  605,
  656,
  657,
  658,
  659,
  660,
  663,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 56 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 56 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (33, 1), (36, 1), (39, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (24, 1), (36, 1), (44, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (10, 1), (36, 2), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (10, 1), (22, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (29, 1), (36, 1), (49, 1), (54, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (30, 1), (36, 1), (41, 1), (49, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (23, 1), (36, 1), (49, 1), (54, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (36, 1), (49, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (41, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (30, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (10, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (52, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (10, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (52, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (49, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (49, 1), (51, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (29, 1), (36, 1), (49, 1), (51, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (29, 1), (36, 1), (49, 1), (51, 1), (54, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (30, 1), (36, 1), (41, 1), (49, 1), (51, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (30, 1), (36, 1), (41, 1), (49, 1), (51, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (52, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (52, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (23, 1), (36, 1), (49, 1), (51, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (23, 1), (36, 1), (49, 1), (51, 1), (54, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (49, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (49, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (41, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (41, 1), (49, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (49, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (49, 1), (51, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (47, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (36, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (26, 1), (36, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (41, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (46, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (52, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (36, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (30, 1), (36, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (10, 1), (18, 1), (22, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (30, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (20, 1), (22, 1), (29, 1), (36, 1), (49, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (20, 1), (22, 1), (30, 1), (36, 1), (41, 1), (49, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (20, 1), (22, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (23, 1), (36, 1), (49, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (30, 1), (36, 1), (49, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (30, 1), (41, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (30, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (30, 1), (36, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (30, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (22, 1), (36, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (22, 1), (36, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (23, 1), (36, 1), (49, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (24, 1), (36, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (26, 1), (36, 1), (49, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (36, 1), (49, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (49, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (23, 1), (36, 1), (49, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (23, 1), (26, 1), (36, 1), (49, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (46, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (30, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (26, 1), (36, 1), (49, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (22, 1), (36, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (22, 1), (30, 1), (36, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (10, 1), (18, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (30, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (20, 1), (22, 1), (29, 1), (36, 1), (49, 1), (51, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (20, 1), (22, 1), (30, 1), (36, 1), (41, 1), (49, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (20, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (23, 1), (36, 1), (49, 1), (51, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (29, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (30, 1), (41, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (30, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (30, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (22, 1), (36, 1), (49, 1), (53, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (26, 1), (36, 1), (37, 1), (49, 1), (53, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (26, 1), (36, 1), (49, 1), (51, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (26, 1), (36, 1), (49, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (39, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (49, 1), (51, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(20, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(26, 1), (37, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (10, 1), (22, 1), (36, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (10, 1), (22, 1), (36, 2), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (30, 1), (36, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (30, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (10, 1), (22, 1), (33, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (22, 1), (24, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (10, 1), (12, 1), (22, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (10, 1), (18, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (30, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (22, 1), (29, 1), (36, 1), (49, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (22, 1), (30, 1), (36, 1), (41, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (22, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (22, 1), (23, 1), (36, 1), (49, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (12, 1), (22, 1), (30, 1), (36, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (20, 1), (22, 1), (29, 1), (36, 1), (49, 1), (51, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (20, 1), (22, 1), (30, 1), (36, 1), (41, 1), (49, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (20, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (23, 1), (36, 1), (49, 1), (51, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (18, 1), (22, 1), (30, 1), (36, 1), (49, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (30, 1), (41, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (30, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 56,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_2_2_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_2_2_5
