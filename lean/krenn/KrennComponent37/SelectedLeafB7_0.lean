import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0214b4b8cec0c2a1cd16f9422bb5f90f77d44d04246ff4826bf3f8ca96bb2062"
def certificateSHA256 : String := "6b480d2e93107d432f2e139e92c52c5c5af6b091fab71b64645c284911a1bc15"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 664 := ![
  0,
  1,
  2,
  3,
  4,
  32,
  149,
  152,
  171,
  179,
  181,
  221,
  294,
  296,
  297,
  301,
  308,
  312,
  318,
  349,
  393,
  424,
  427,
  440,
  446,
  447,
  454,
  466,
  474,
  476,
  478,
  541,
  555,
  566,
  580,
  584,
  602,
  603,
  606,
  607,
  628,
  629,
  646,
  655,
  657,
  658,
  659,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (51, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (47, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (29, 1), (31, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (33, 1), (44, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (29, 1), (31, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (44, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (23, 1), (31, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (25, 1), (33, 1), (44, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 1), (44, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (23, 1), (31, 1), (47, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (31, 1), (44, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (44, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (36, 1), (37, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (31, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (31, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (43, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (44, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (33, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (31, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (31, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (31, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (31, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (55, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (30, 1), (31, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (29, 1), (31, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (33, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (48, 1), (51, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (29, 1), (31, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (23, 1), (31, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (25, 1), (33, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (23, 1), (31, 1), (47, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (50, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (43, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (23, 1), (31, 1), (44, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (43, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (31, 1), (44, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (37, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (30, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (33, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (13, 1), (26, 1), (33, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (33, 1), (43, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (33, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (34, 1), (37, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (30, 1), (31, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (31, 1), (44, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (30, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }]
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

#print axioms Krenn.Component37.SelectedLeafB7_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB7_0
