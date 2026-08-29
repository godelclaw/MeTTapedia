import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_0_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "28b298712b6dc7d5a318438dfe656606a413e3b62923a19c98750fd5af1d573e"
def certificateSHA256 : String := "c0530ead82b1aa1fc94b4d4ad9882219dab3bfdb608a9915b6cee8b9688f2b59"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 48 → Fin 670 := ![
  17,
  151,
  167,
  168,
  171,
  175,
  176,
  178,
  180,
  183,
  280,
  294,
  295,
  296,
  297,
  300,
  301,
  302,
  310,
  313,
  315,
  340,
  343,
  411,
  424,
  433,
  446,
  450,
  478,
  481,
  482,
  591,
  602,
  603,
  612,
  646,
  647,
  655,
  657,
  658,
  660,
  661,
  662,
  663,
  664,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 48 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 48 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (23, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (21, 1), (23, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (23, 1), (43, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (23, 1), (25, 1), (43, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (20, 1), (23, 1), (33, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (21, 1), (23, 1), (33, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (23, 1), (33, 1), (43, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (25, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (33, 1), (34, 1), (37, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (21, 1), (28, 1), (44, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (25, 1), (28, 1), (49, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (43, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (17, 1), (21, 1), (28, 1), (33, 1), (44, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (17, 1), (25, 1), (28, 1), (33, 1), (49, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (43, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (49, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (39, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (28, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (21, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (21, 1), (26, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (45, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (46, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (20, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (21, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (43, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (20, 1), (33, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (21, 1), (33, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (33, 1), (43, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (17, 1), (21, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (25, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (21, 1), (33, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (25, 1), (33, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (23, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (26, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (48, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (33, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (33, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (21, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (44, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (47, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (37, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (37, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (20, 1), (33, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (21, 1), (33, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (33, 1), (37, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 2), (21, 1), (44, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 2), (25, 1), (49, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (34, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (21, 1), (33, 1), (44, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (25, 1), (33, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (18, 1), (20, 1), (28, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (18, 1), (21, 1), (28, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (25, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (21, 1), (28, 1), (30, 1), (44, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (25, 1), (28, 1), (30, 1), (49, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (21, 1), (28, 1), (43, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (25, 1), (28, 1), (43, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (28, 1), (34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (30, 1), (43, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (30, 1), (34, 1), (37, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (18, 1), (20, 1), (28, 1), (33, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (18, 1), (21, 1), (28, 1), (33, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (25, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (21, 1), (28, 1), (30, 1), (33, 1), (44, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (25, 1), (28, 1), (30, 1), (33, 1), (49, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (21, 1), (28, 1), (33, 1), (43, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (25, 1), (28, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (28, 1), (33, 1), (34, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (30, 1), (33, 1), (43, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (33, 1), (34, 1), (37, 1), (49, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (49, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (20, 1), (33, 1), (49, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (34, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (25, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (21, 1), (23, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (26, 1), (44, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (33, 1), (34, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (20, 1), (25, 1), (33, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (26, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (26, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (31, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (17, 1), (21, 1), (28, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (17, 1), (25, 1), (28, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (25, 1), (43, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (34, 1), (37, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (17, 1), (21, 1), (28, 1), (33, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (17, 1), (25, 1), (28, 1), (33, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (25, 1), (33, 1), (43, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (37, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 48,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_0_2_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_0_2_5
