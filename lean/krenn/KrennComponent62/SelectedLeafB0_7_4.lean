import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB0_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e0f55e5a9f6ad8d1a36fbfffb1d70d0a7bd11f8c22237f2910690ef8dca2f662"
def certificateSHA256 : String := "57bb59a0b59b763512ed35689f67d84f48276bacdfd07cec4adb6ef9c1eba60f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 667 := ![
  18,
  21,
  150,
  153,
  155,
  158,
  223,
  226,
  295,
  301,
  302,
  309,
  311,
  315,
  316,
  390,
  407,
  408,
  414,
  437,
  439,
  441,
  444,
  453,
  454,
  455,
  457,
  470,
  473,
  478,
  480,
  510,
  515,
  544,
  557,
  578,
  600,
  601,
  610,
  631,
  646,
  655,
  657,
  658,
  660,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (12, 1), (28, 1), (43, 1), (52, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (12, 1), (52, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (28, 1), (43, 1), (48, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (48, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (28, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (37, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (17, 1), (28, 1), (43, 1), (45, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (17, 1), (45, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (31, 1), (45, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (17, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (23, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (28, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (31, 1), (37, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (22, 1), (24, 1), (31, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (24, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (19, 1), (24, 1), (33, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (24, 1), (33, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (27, 1), (31, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (19, 1), (24, 1), (33, 1), (47, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (33, 1), (45, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (31, 1), (46, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (27, 1), (31, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (27, 1), (31, 1), (47, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (17, 1), (23, 1), (28, 1), (43, 1), (53, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (17, 1), (23, 1), (53, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (17, 1), (23, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (23, 2), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (23, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (23, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (24, 1), (33, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (27, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (33, 1), (45, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (31, 1), (46, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (19, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (27, 1), (28, 1), (43, 1), (44, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (27, 1), (44, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (27, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (27, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (45, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (6, 1), (28, 1), (43, 1), (53, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (53, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (46, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (23, 1), (24, 1), (33, 1), (45, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (23, 1), (27, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (23, 1), (24, 1), (33, 1), (45, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (27, 1), (31, 1), (46, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (6, 1), (22, 1), (23, 1), (28, 1), (43, 1), (53, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (22, 1), (23, 1), (53, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (22, 1), (23, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (23, 2), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (23, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (23, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (45, 1), (50, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (45, 1), (57, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (22, 1), (31, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (22, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (19, 1), (24, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (24, 1), (33, 1), (45, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (27, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (19, 1), (24, 1), (33, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (33, 1), (45, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (27, 1), (31, 1), (46, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (19, 1), (24, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (19, 1), (24, 1), (33, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (22, 1), (28, 1), (43, 1), (53, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (22, 1), (53, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (22, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (24, 1), (33, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (24, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (27, 1), (28, 1), (41, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (27, 1), (41, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (27, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (27, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (28, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (31, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (19, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (24, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (33, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (27, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (22, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (19, 1), (23, 1), (24, 1), (33, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (19, 1), (23, 1), (24, 1), (33, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (6, 1), (17, 1), (28, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (17, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (17, 1), (28, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (16, 1), (24, 1), (33, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (24, 1), (33, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (18, 1), (27, 1), (28, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (27, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (18, 1), (27, 1), (28, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (23, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (22, 1), (24, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (22, 1), (24, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (28, 1), (50, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (57, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (27, 1), (28, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (27, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (27, 1), (28, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (43, 1), (50, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (43, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (27, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (27, 1), (31, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (24, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (33, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (28, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (28, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (24, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (33, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (6, 1), (12, 1), (28, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (12, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (28, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (16, 1), (24, 1), (33, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (27, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (16, 1), (24, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (27, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (50, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (18, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (33, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (28, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (28, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (31, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (28, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (27, 1), (28, 1), (35, 1), (43, 1), (54, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (27, 1), (28, 1), (43, 1), (44, 1), (51, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (18, 1), (27, 1), (35, 1), (57, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (18, 1), (27, 1), (44, 1), (51, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (27, 1), (28, 1), (41, 1), (43, 1), (51, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (27, 1), (41, 1), (51, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (12, 1), (19, 1), (24, 1), (33, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (16, 1), (24, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (16, 1), (24, 1), (33, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (19, 1), (24, 1), (33, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (22, 1), (24, 1), (31, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (22, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (27, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (27, 1), (31, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (27, 1), (31, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (19, 1), (24, 1), (33, 1), (42, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (16, 1), (24, 1), (33, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (16, 1), (24, 1), (33, 1), (45, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (24, 1), (33, 1), (42, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (22, 1), (24, 1), (31, 1), (43, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (22, 1), (31, 1), (43, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (27, 1), (31, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (27, 1), (31, 1), (45, 1), (47, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (27, 1), (31, 1), (45, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (28, 1), (43, 1), (50, 1), (51, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (43, 1), (51, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (28, 1), (35, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (28, 1), (38, 1), (43, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (28, 1), (43, 2), (50, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (35, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (38, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (39, 1), (50, 1), (54, 1), (55, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (43, 2), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (43, 1), (50, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (45, 1), (50, 1), (51, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (39, 1), (55, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (43, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (45, 1), (51, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (18, 1), (27, 1), (28, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (18, 1), (27, 1), (28, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (27, 1), (28, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (23, 1), (27, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (23, 1), (27, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (35, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (40, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (31, 1), (35, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (31, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (27, 1), (41, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (28, 1), (40, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (31, 1), (37, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (39, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (45, 1), (51, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (51, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1), (39, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (40, 1)] }, { coefficient := -1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (6, 1), (28, 1), (36, 1), (43, 1), (54, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (28, 1), (39, 1), (43, 1), (54, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (36, 1), (57, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (39, 1), (56, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (28, 1), (43, 1), (50, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (43, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (50, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (18, 1), (27, 1), (28, 1), (41, 1), (43, 1), (48, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (27, 1), (41, 1), (48, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (17, 1), (22, 1), (23, 1), (28, 1), (43, 1), (53, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (17, 1), (22, 1), (23, 1), (53, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (13, 1), (18, 1), (19, 1), (24, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (12, 1), (13, 1), (18, 1), (24, 1), (33, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (13, 1), (19, 1), (24, 1), (33, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (12, 1), (13, 1), (23, 1), (24, 1), (33, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (18, 1), (27, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (23, 1), (27, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (16, 1), (19, 1), (23, 1), (24, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (16, 1), (19, 1), (24, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (22, 1), (24, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (13, 1), (18, 1), (19, 1), (24, 1), (33, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (13, 1), (18, 1), (24, 1), (33, 1), (45, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (13, 1), (19, 1), (24, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (13, 1), (23, 1), (24, 1), (33, 1), (45, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (27, 1), (31, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (27, 1), (31, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (16, 1), (19, 1), (23, 1), (24, 1), (33, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (16, 1), (19, 1), (24, 1), (33, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (22, 1), (24, 1), (31, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (28, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (18, 1), (27, 1), (28, 1), (41, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (23, 1), (27, 1), (41, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (40, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (31, 1), (37, 1), (41, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (17, 1), (22, 1), (23, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (22, 1), (23, 2), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (23, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (23, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (6, 1), (28, 1), (30, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (6, 1), (30, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (9, 1), (30, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (30, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (13, 1), (28, 1), (30, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (23, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (28, 1), (30, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (31, 1), (37, 1)] }]
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

#print axioms Krenn.Component62.SelectedLeafB0_7_4.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB0_7_4
