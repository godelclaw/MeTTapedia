import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_2_3_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1277a5a3e4e51190b9178d83aa069ab30c0e7ee8912623e2e8be1721e14f872b"
def certificateSHA256 : String := "261967576df80187c8d7609794d1a6e468bad2395a52d3c60d66a242dd529478"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 673 := ![
  11,
  13,
  14,
  17,
  18,
  56,
  109,
  139,
  150,
  158,
  159,
  207,
  301,
  302,
  311,
  401,
  444,
  454,
  550,
  557,
  589,
  600,
  601,
  605,
  619,
  655,
  656,
  657,
  659,
  660,
  661,
  663,
  664,
  666,
  667,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(21, 1), (24, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (26, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (30, 1), (40, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (32, 1), (35, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (18, 1), (26, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (18, 1), (30, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (26, 1), (30, 1), (40, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (30, 1), (32, 1), (35, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (30, 1), (31, 1), (34, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (32, 1), (34, 1), (35, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (14, 1), (21, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (26, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (32, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(29, 1), (43, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(29, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (26, 1), (31, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (31, 1), (32, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (23, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (29, 1), (43, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (29, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (38, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (50, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(29, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (22, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (14, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (16, 1), (21, 1), (55, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (21, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (21, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(14, 1), (32, 1), (35, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (21, 1), (22, 1), (24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (26, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (30, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (30, 1), (40, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (32, 1), (35, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (21, 1), (22, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (17, 1), (21, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (26, 1), (43, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (22, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (14, 1), (21, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (26, 1), (43, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (21, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (26, 1), (30, 1), (43, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 1), (32, 1), (35, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (26, 1), (30, 1), (40, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 1), (32, 1), (35, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (21, 1), (55, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (32, 1), (35, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (55, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (21, 1), (36, 1), (55, 1), (58, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(14, 1), (21, 1), (45, 1), (52, 1), (55, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (46, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (32, 1), (35, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (14, 1), (26, 1), (30, 1), (31, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (14, 1), (30, 1), (31, 1), (32, 1), (35, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (26, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (21, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (26, 1), (33, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (32, 1), (33, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (14, 1), (26, 1), (30, 1), (37, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (14, 1), (30, 1), (32, 1), (35, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (28, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (28, 1), (30, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (14, 1), (18, 1), (26, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (14, 1), (18, 1), (30, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (18, 1), (26, 1), (30, 1), (43, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (18, 1), (30, 1), (32, 1), (35, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (55, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (50, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (21, 1), (55, 1), (58, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (21, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (26, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (21, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (32, 1), (35, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (21, 1), (45, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (21, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (26, 1), (43, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (32, 1), (35, 1), (45, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (14, 1), (26, 1), (30, 1), (34, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (14, 1), (30, 1), (32, 1), (34, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (23, 1), (26, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (23, 1), (30, 1), (32, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (14, 1), (18, 1), (26, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (14, 1), (18, 1), (30, 1), (32, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (14, 1), (21, 1), (22, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_2_3_6_3.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_2_3_6_3
