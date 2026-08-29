import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ee8853d9d9c71107ac81caeecb3d0bc4d43492d76bffe8bca85bc023d79f05a3"
def certificateSHA256 : String := "85f58c400b70f15bd597fd05cd641c302a192fc66977eada7b455e7eebc19c79"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 642 := ![
  2,
  3,
  4,
  9,
  10,
  11,
  12,
  14,
  17,
  18,
  20,
  21,
  23,
  24,
  122,
  174,
  175,
  180,
  183,
  184,
  192,
  196,
  204,
  209,
  232,
  265,
  278,
  344,
  345,
  347,
  351,
  353,
  355,
  359,
  363,
  364,
  366,
  369,
  390,
  405,
  410,
  460,
  462,
  511,
  581,
  608,
  634,
  635,
  636,
  637,
  638,
  639,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(4, 1), (25, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (32, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (20, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (22, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (20, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (26, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (32, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (26, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (34, 1), (37, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (26, 1), (29, 1), (55, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (30, 1), (32, 1), (38, 1), (43, 1), (51, 2), (61, 2)] }],
  [{ coefficient := -2, powers := [(4, 1), (29, 1), (31, 1), (45, 1), (47, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (29, 1), (34, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (20, 1), (29, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (29, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (29, 1), (34, 1), (37, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (22, 1), (31, 1), (43, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (31, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (34, 1), (43, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (34, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (31, 1), (43, 1), (45, 2)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (31, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (34, 1), (40, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (34, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (22, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (26, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (22, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (26, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (34, 1), (37, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (21, 1), (31, 1), (45, 1), (47, 1)] }, { coefficient := -2, powers := [(8, 1), (21, 1), (34, 1), (40, 1), (47, 1)] }, { coefficient := -2, powers := [(16, 1), (21, 1), (31, 1), (38, 1), (45, 1)] }, { coefficient := -2, powers := [(16, 1), (21, 1), (34, 1), (38, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (22, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (18, 1), (29, 1), (31, 1), (45, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (18, 1), (29, 1), (34, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (22, 1), (31, 1), (45, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(4, 1), (22, 1), (34, 1), (45, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (22, 1), (45, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (26, 1), (45, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (30, 1), (32, 1), (38, 1), (50, 1), (51, 1), (61, 2)] }, { coefficient := -2, powers := [(10, 1), (18, 1), (20, 1), (29, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (22, 1), (26, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(10, 1), (22, 1), (34, 1), (37, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(14, 1), (18, 1), (20, 1), (29, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (29, 1), (34, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (34, 1), (37, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (29, 1), (31, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (29, 1), (34, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (29, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (24, 1), (26, 1), (32, 1), (50, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (29, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (31, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (34, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (29, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (29, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (29, 1), (34, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (29, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (29, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (29, 1), (31, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(10, 1), (16, 1), (22, 1), (55, 1)] }, { coefficient := -2, powers := [(14, 1), (16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (22, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (31, 1), (45, 1), (47, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (40, 1), (47, 1)] }, { coefficient := 2, powers := [(16, 1), (31, 1), (38, 1), (45, 1)] }, { coefficient := 2, powers := [(16, 1), (34, 1), (38, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (47, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (26, 1), (32, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (18, 1), (29, 1), (31, 1), (45, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (18, 1), (29, 1), (34, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (18, 1), (20, 1), (29, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(14, 1), (18, 1), (20, 1), (29, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (29, 1), (34, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (17, 1), (22, 1), (31, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (22, 1), (34, 1), (51, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (29, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (22, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (12, 1), (22, 1), (31, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (22, 1), (34, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (32, 1), (50, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (31, 1), (45, 2)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (34, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (22, 1), (34, 1), (37, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (11, 1), (26, 1), (32, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (12, 1), (31, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (16, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (14, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (26, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (22, 1), (31, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (34, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (11, 1), (26, 1), (30, 1), (32, 1), (38, 1), (51, 2), (61, 2)] }],
  [{ coefficient := 2, powers := [(4, 1), (12, 1), (29, 1), (31, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (12, 1), (29, 1), (34, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(10, 1), (12, 1), (20, 1), (29, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (20, 1), (29, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (29, 1), (34, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (16, 1), (22, 1), (31, 1), (45, 1), (51, 1)] }, { coefficient := 2, powers := [(4, 1), (16, 1), (22, 1), (34, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (22, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (22, 1), (26, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(10, 1), (16, 1), (22, 1), (26, 1), (45, 1), (55, 1)] }, { coefficient := 2, powers := [(10, 1), (16, 1), (22, 1), (34, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (22, 1), (34, 1), (37, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (51, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (30, 1), (32, 1), (38, 1), (51, 1), (61, 2)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (20, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (20, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (20, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (11, 1), (26, 1), (30, 1), (32, 1), (38, 1), (51, 1), (61, 2)] }],
  [{ coefficient := 2, powers := [(4, 1), (16, 1), (22, 1), (31, 1), (51, 1)] }, { coefficient := -2, powers := [(4, 1), (16, 1), (22, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (22, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (22, 1), (26, 1), (58, 1)] }, { coefficient := 2, powers := [(10, 1), (16, 1), (22, 1), (26, 1), (55, 1)] }, { coefficient := -2, powers := [(10, 1), (16, 1), (22, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (22, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (23, 1), (26, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (29, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (22, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (26, 1), (29, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (32, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (12, 1), (29, 1), (31, 1), (45, 1), (47, 1)] }, { coefficient := 2, powers := [(4, 1), (12, 1), (29, 1), (34, 1), (47, 1), (51, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (20, 1), (29, 1), (47, 1), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (20, 1), (29, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (29, 1), (34, 1), (37, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (41, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 3, powers := [(7, 1), (20, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -3, powers := [(7, 1), (26, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (38, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (41, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (41, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (34, 1), (37, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (41, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (41, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (26, 1), (30, 1), (32, 1), (38, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (31, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (34, 1), (35, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (29, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (29, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (20, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (26, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (35, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (34, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (26, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (29, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (29, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (35, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (26, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (20, 1), (35, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (26, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (31, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (20, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (26, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (29, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (26, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (29, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (29, 1), (34, 1), (37, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB4_6.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB4_6
