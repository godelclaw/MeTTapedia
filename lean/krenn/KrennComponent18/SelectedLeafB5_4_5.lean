import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4764d78c8986c6470b5d6f4c55f6ab82081cf76f8fddbcc748d41b192d8bf97e"
def certificateSHA256 : String := "41e8af3d780308bbcfa3b0473de8d3e1652001628d53819270566cdc717c4b08"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 667 := ![
  5,
  6,
  9,
  10,
  11,
  13,
  16,
  17,
  19,
  142,
  147,
  167,
  300,
  301,
  302,
  318,
  322,
  343,
  409,
  433,
  437,
  438,
  443,
  478,
  479,
  581,
  585,
  590,
  602,
  603,
  610,
  646,
  655,
  657,
  660,
  662,
  663,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (19, 1), (29, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (19, 1), (23, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (40, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (26, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (37, 1), (40, 1), (59, 1), (64, 2)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1), (64, 2)] }, { coefficient := -1, powers := [(14, 1), (37, 1), (40, 1), (64, 2)] }, { coefficient := -1, powers := [(24, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (14, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (14, 1), (49, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (14, 1), (32, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (19, 1), (49, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (14, 1), (32, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (14, 1), (19, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (14, 1), (25, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (19, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (19, 1), (49, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (25, 1), (41, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (19, 1), (29, 1), (49, 1), (54, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (14, 1), (29, 1), (32, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (14, 1), (25, 1), (29, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (19, 1), (29, 1), (49, 1), (50, 1), (54, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (19, 1), (23, 1), (49, 1), (54, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (14, 1), (23, 1), (32, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (14, 1), (23, 1), (25, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (19, 1), (23, 1), (49, 1), (50, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (25, 1), (34, 1), (40, 1), (47, 1), (59, 1), (64, 2)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (40, 1), (60, 1), (64, 2)] }, { coefficient := -2, powers := [(14, 1), (24, 1), (25, 1), (47, 1), (54, 1), (64, 2)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (45, 1), (54, 1), (64, 2)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1), (60, 1), (64, 2)] }],
  [{ coefficient := 1, powers := [(14, 1), (17, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (35, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (44, 1), (49, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (14, 1), (35, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (38, 1), (49, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (40, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (17, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (19, 1), (49, 1), (54, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (14, 1), (32, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (14, 1), (25, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (19, 1), (49, 1), (50, 1), (54, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (31, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (19, 1), (49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (49, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (14, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (25, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (49, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (14, 1), (34, 1), (40, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (24, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (14, 1), (40, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (24, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (40, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (40, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (35, 1), (49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (14, 1), (41, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 2), (14, 1), (19, 1), (41, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (14, 1), (32, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (14, 1), (19, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (19, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (14, 1), (49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 2), (49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (25, 1), (49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (14, 1), (35, 1), (49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (19, 1), (44, 1), (49, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (14, 1), (32, 1), (44, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (14, 1), (25, 1), (44, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 2), (19, 1), (41, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (19, 1), (38, 1), (49, 1), (54, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (14, 1), (41, 1), (49, 1), (54, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 2), (14, 1), (19, 1), (41, 1), (49, 1), (54, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (14, 1), (32, 1), (49, 1), (54, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (14, 1), (35, 1), (41, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (14, 1), (19, 1), (49, 1), (54, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (14, 2), (25, 1), (41, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 2), (6, 1), (14, 1), (19, 1), (35, 1), (41, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 2), (14, 2), (19, 1), (25, 1), (41, 1), (49, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (6, 1), (14, 1), (32, 1), (35, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (14, 2), (25, 1), (32, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (19, 1), (35, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (14, 2), (19, 1), (25, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (35, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (34, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (18, 1), (25, 1), (34, 1), (40, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (64, 1)] }, { coefficient := -2, powers := [(14, 1), (18, 1), (24, 1), (25, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (31, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (14, 1), (37, 1), (40, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (17, 1), (25, 1), (34, 1), (40, 1), (47, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (31, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (37, 1), (40, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (23, 1), (40, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (24, 1), (25, 1), (47, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (24, 1), (45, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (29, 1), (40, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (14, 1), (35, 1), (41, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (6, 1), (14, 1), (32, 1), (35, 1), (49, 1), (54, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB5_4_5.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_4_5
