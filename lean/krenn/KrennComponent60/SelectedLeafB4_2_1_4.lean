import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7c7307b2d6ccbbc4505f91e9bff94c277685d33d84d82be1a402cff2c6e25b24"
def certificateSHA256 : String := "3f39a8145c1c36d1f122fe9e63a4e9588bd2ae36a0c6b3824f5afc7210c622b5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 668 := ![
  7,
  22,
  147,
  149,
  171,
  177,
  178,
  186,
  206,
  301,
  302,
  303,
  310,
  312,
  359,
  404,
  423,
  425,
  432,
  443,
  454,
  556,
  579,
  582,
  600,
  601,
  621,
  653,
  655,
  656,
  658,
  659,
  661,
  662,
  663,
  664,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (25, 1), (30, 1), (42, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (30, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (36, 1), (42, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1), (49, 1), (53, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (21, 1), (36, 1), (49, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (36, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (25, 1), (42, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (32, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (36, 1), (42, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (32, 1), (36, 1), (42, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (32, 1), (36, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (36, 1), (49, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (36, 1), (49, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (33, 1), (36, 1), (49, 1), (54, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (33, 1), (36, 1), (49, 1), (57, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (36, 1), (49, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (30, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (36, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (49, 1), (54, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (30, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (36, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (48, 1), (49, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (33, 1), (36, 1), (49, 1), (54, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (26, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (42, 1), (49, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (32, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(25, 1), (32, 1), (36, 1), (42, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (49, 1), (54, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (32, 1), (36, 1), (49, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (43, 1), (49, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (36, 1), (49, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (49, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (25, 1), (30, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (36, 1), (49, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (33, 1), (36, 1), (49, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (42, 1), (43, 1), (49, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 2), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (42, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (36, 1), (49, 1), (57, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (30, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1), (49, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (36, 1), (38, 1), (49, 1), (57, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (36, 1), (47, 1), (49, 1), (53, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (30, 1), (38, 1), (42, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (30, 1), (42, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(21, 1), (36, 1), (42, 1), (49, 1), (50, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (36, 1), (38, 1), (42, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (36, 1), (42, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (38, 1), (49, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (48, 1), (49, 1), (54, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (26, 1), (36, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 2), (42, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (25, 1), (26, 1), (42, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (26, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (25, 1), (26, 1), (32, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (26, 1), (32, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (32, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (26, 1), (36, 1), (42, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (26, 1), (32, 1), (36, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (25, 1), (30, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (30, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (30, 1), (36, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (36, 1), (49, 1), (57, 2), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (25, 1), (30, 1), (35, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (30, 1), (35, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (35, 1), (36, 1), (49, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (32, 1), (36, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(20, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (36, 1), (49, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 2), (30, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (26, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (25, 2), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (33, 1), (36, 1), (49, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (26, 1), (42, 1), (43, 1), (49, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (42, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (36, 1), (47, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (36, 1), (49, 1), (57, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (25, 1), (30, 1), (42, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (36, 1), (42, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (36, 1), (49, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (25, 1), (30, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (25, 1), (30, 1), (41, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (30, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (36, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1), (48, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (30, 1), (36, 1), (41, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (47, 1), (49, 1), (50, 1), (57, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_1_4.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_1_4
