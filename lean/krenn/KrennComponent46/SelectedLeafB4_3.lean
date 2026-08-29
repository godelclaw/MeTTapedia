import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component46.SelectedLeafB4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b8ec6a35e9be8290c0da0c8fc324e6aca4bbaf9255ece2476485e3cfe4762759"
def certificateSHA256 : String := "8774120d1b4cea03397133dcf6c9c399336efeab46ac88e29527974dd4d9c591"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 646 := ![
  2,
  3,
  4,
  5,
  7,
  9,
  11,
  14,
  17,
  22,
  27,
  29,
  33,
  62,
  162,
  164,
  172,
  174,
  200,
  202,
  203,
  211,
  229,
  240,
  252,
  350,
  354,
  361,
  362,
  367,
  478,
  507,
  581,
  582,
  585,
  586,
  587,
  609,
  611,
  618,
  637,
  638,
  639,
  640,
  641,
  642,
  643,
  644,
  645
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 2), (7, 1), (25, 1), (31, 1), (34, 1), (43, 1), (57, 1), (59, 2), (63, 1)] }, { coefficient := 1, powers := [(5, 2), (7, 1), (31, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (43, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (26, 1), (29, 1), (34, 1), (43, 1), (57, 1), (59, 2), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (26, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (43, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (38, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (37, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (43, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (37, 1), (38, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (43, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (22, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (37, 1), (43, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (37, 1), (43, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (43, 1), (53, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (34, 1), (43, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (25, 1), (34, 1), (43, 1), (47, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 2), (34, 1), (36, 1), (43, 1), (47, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (43, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (43, 1), (53, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (29, 1), (34, 1), (43, 1), (53, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (34, 1), (36, 1), (43, 1), (52, 1), (53, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (26, 1), (29, 1), (34, 1), (43, 1), (46, 1), (54, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (26, 1), (34, 1), (36, 1), (43, 1), (46, 1), (52, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (25, 1), (26, 1), (34, 1), (43, 1), (46, 1), (54, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (26, 1), (34, 1), (36, 1), (43, 1), (46, 1), (52, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (46, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (43, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (9, 1), (37, 1), (43, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (37, 1), (43, 1), (44, 1), (50, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (37, 1), (43, 1), (50, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (37, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (29, 1), (34, 2), (43, 1), (49, 1), (57, 1), (59, 1), (61, 1), (63, 2)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (34, 2), (36, 1), (43, 1), (49, 1), (52, 1), (57, 1), (61, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (25, 1), (34, 1), (43, 1), (56, 1), (57, 1), (59, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (29, 1), (34, 1), (43, 1), (46, 1), (57, 1), (59, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (36, 1), (39, 1), (43, 1), (57, 1), (59, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (25, 1), (34, 1), (43, 1), (56, 2), (57, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (29, 1), (34, 1), (43, 1), (46, 1), (56, 1), (57, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (36, 1), (39, 1), (43, 1), (56, 1), (57, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (25, 1), (34, 1), (43, 1), (52, 1), (56, 1), (57, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (29, 1), (34, 1), (43, 1), (46, 1), (52, 1), (57, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (34, 1), (36, 1), (39, 1), (43, 1), (52, 1), (57, 1), (63, 2)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (15, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (37, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (37, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (43, 1), (49, 1), (61, 1), (63, 2)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1), (50, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (12, 1), (25, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (12, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (37, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (37, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (37, 1), (38, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (43, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (29, 1), (34, 2), (43, 1), (57, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (34, 2), (36, 1), (43, 1), (52, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (21, 1), (26, 1), (29, 1), (34, 1), (43, 1), (46, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (21, 1), (26, 1), (34, 1), (36, 1), (43, 1), (46, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (25, 1), (26, 1), (34, 1), (43, 1), (46, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (26, 1), (34, 1), (36, 1), (43, 1), (46, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (43, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (29, 1), (34, 1), (43, 1), (54, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 2), (34, 1), (36, 1), (43, 1), (52, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (29, 1), (34, 1), (43, 2), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (34, 1), (36, 1), (43, 2), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (25, 1), (34, 1), (43, 1), (57, 2), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 2), (34, 1), (36, 1), (43, 1), (52, 1), (57, 2), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (18, 1), (25, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (18, 1), (29, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (36, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (33, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (12, 1), (25, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 2), (12, 1), (29, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (21, 1), (26, 1), (29, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (21, 1), (26, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (25, 1), (26, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (26, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (7, 1), (25, 1), (34, 1), (43, 1), (57, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 2), (7, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (43, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (29, 1), (34, 1), (43, 1), (57, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (43, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (34, 1), (43, 1), (54, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (36, 1), (43, 1), (52, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (34, 1), (43, 1), (54, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (36, 1), (43, 1), (52, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (33, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (36, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (21, 1), (29, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (21, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (25, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (14, 1), (29, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (14, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (14, 1), (25, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (14, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (36, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (34, 1), (43, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (34, 1), (43, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (39, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (43, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (34, 1), (43, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (29, 1), (34, 1), (43, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (36, 1), (39, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (34, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (29, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 2), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (25, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (29, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (25, 1), (34, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (36, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (29, 1), (34, 2), (43, 1), (49, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (34, 2), (36, 1), (43, 1), (49, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (43, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (42, 1), (43, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (43, 1), (46, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (34, 1), (40, 1), (43, 1), (57, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (34, 1), (43, 2), (57, 2), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (36, 1), (40, 1), (43, 1), (52, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (36, 1), (43, 2), (52, 1), (57, 2), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (34, 1), (40, 1), (43, 1), (57, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (34, 1), (43, 2), (57, 2), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (36, 1), (40, 1), (43, 1), (52, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (36, 1), (43, 2), (52, 1), (57, 2), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(43, 2), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (37, 1), (43, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (9, 1), (35, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (35, 1), (37, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (37, 1), (38, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (9, 1), (27, 1), (37, 1), (43, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (27, 1), (37, 1), (43, 1), (44, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (27, 1), (37, 1), (43, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (27, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (29, 1), (34, 2), (43, 1), (49, 1), (57, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (34, 2), (36, 1), (43, 1), (49, 1), (52, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (27, 1), (34, 1), (43, 1), (56, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (27, 1), (29, 1), (34, 1), (43, 1), (46, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (27, 1), (34, 1), (36, 1), (39, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (25, 1), (27, 1), (34, 1), (43, 1), (56, 2), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (27, 1), (29, 1), (34, 1), (43, 1), (46, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (27, 1), (34, 1), (36, 1), (39, 1), (43, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (25, 1), (27, 1), (34, 1), (43, 1), (52, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (27, 1), (29, 1), (34, 1), (43, 1), (46, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (27, 1), (34, 1), (36, 1), (39, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (9, 1), (35, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (27, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (34, 1), (43, 1), (49, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (37, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 49,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component46.SelectedLeafB4_3.selectedHasNoCommonZero

end Krenn.Component46.SelectedLeafB4_3
