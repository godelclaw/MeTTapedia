import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_1_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4f26355ee5a41e2ee1c793d2cd5d2ad8ff0deced21d07b5b750c1d380faa3d76"
def certificateSHA256 : String := "cdf6b71c1154c72de61ecb7f3e7548312370bc2f807c2336b46248cf2b452dd2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 670 := ![
  18,
  147,
  153,
  226,
  294,
  301,
  302,
  318,
  408,
  414,
  439,
  442,
  444,
  454,
  455,
  467,
  468,
  515,
  526,
  549,
  557,
  558,
  559,
  581,
  600,
  601,
  631,
  649,
  655,
  657,
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
def selectedEquations : Fin 38 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (51, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (34, 1), (39, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (28, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (28, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (31, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (34, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (34, 1), (39, 1), (44, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (31, 1), (34, 1), (44, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (34, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (34, 1), (39, 1), (44, 1), (53, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (33, 1), (34, 1), (39, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (31, 1), (34, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(22, 1), (31, 1), (34, 1), (44, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (13, 1), (28, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (18, 1), (30, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (28, 1), (30, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (39, 1), (53, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (39, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (46, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (13, 1), (28, 1), (30, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (18, 1), (30, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (28, 1), (30, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (22, 1), (34, 1), (39, 1), (53, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (22, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (22, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := -2, powers := [(9, 1), (22, 1), (31, 1), (34, 1), (53, 1)] }, { coefficient := 2, powers := [(22, 1), (31, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (34, 1), (39, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (34, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(22, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (34, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (17, 1), (28, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (33, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (34, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (19, 1), (33, 1), (34, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (33, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (13, 1), (28, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (34, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (33, 1), (34, 1), (39, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (34, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (34, 1), (39, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (34, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (28, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(12, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (47, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (47, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (34, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (19, 1), (33, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (33, 1), (34, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (28, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (36, 1), (39, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (39, 2), (56, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (39, 1), (46, 1), (53, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (28, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (40, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (46, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (24, 1), (33, 1), (34, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (31, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (19, 1), (47, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (12, 1), (19, 1), (31, 1), (33, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (31, 1), (33, 1), (34, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (19, 1), (31, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (19, 1), (24, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (19, 1), (24, 1), (33, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (19, 1), (47, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (34, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (47, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (38, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (19, 1), (33, 1), (34, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (33, 1), (34, 1), (38, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (24, 1), (33, 1), (34, 1), (39, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (19, 1), (38, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (24, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (33, 1), (34, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (34, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (34, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (13, 1), (28, 1), (30, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (28, 1), (30, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (30, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (31, 1), (34, 1), (47, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (22, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (19, 1), (38, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (24, 1), (33, 1), (34, 1), (38, 1), (39, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (34, 1), (39, 1), (44, 1), (53, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (22, 1), (34, 1), (38, 1), (39, 1), (53, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (13, 1), (28, 1), (30, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (18, 1), (30, 1), (46, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (28, 1), (30, 1), (40, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (16, 1), (22, 1), (28, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (17, 1), (22, 1), (28, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (18, 1), (22, 1), (44, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (22, 1), (28, 1), (40, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (22, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (28, 1), (38, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (19, 1), (33, 1), (34, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (19, 1), (33, 1), (34, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (24, 1), (33, 1), (34, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (22, 1), (31, 1), (34, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (24, 1), (33, 1), (34, 1), (39, 1), (42, 1)] }, { coefficient := 2, powers := [(9, 1), (17, 1), (22, 1), (31, 1), (34, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (19, 1), (33, 1), (34, 1), (38, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (19, 1), (38, 1), (47, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (33, 1), (34, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (33, 1), (34, 1), (38, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (31, 1), (34, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (33, 1), (34, 1), (39, 1), (42, 1), (47, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (31, 1), (34, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (39, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (34, 1), (39, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (34, 1), (39, 1), (45, 1), (48, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (13, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (31, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (34, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (28, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (28, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (17, 1), (28, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (45, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (28, 1), (40, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (31, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (31, 1), (34, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (34, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (34, 1), (45, 1), (47, 1), (48, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_1_2_2.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_1_2_2
