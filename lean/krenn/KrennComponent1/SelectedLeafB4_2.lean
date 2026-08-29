import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f8ee1c46e054e3d1ac995a02d3b83c16aedbd9e95e8604d8efa219d7f248baf6"
def certificateSHA256 : String := "df1c903b0b37f7524088dd5a77a453287c8191e3198cc12b7b9137990e74b722"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 43 → Fin 588 := ![
  1,
  15,
  21,
  23,
  25,
  35,
  37,
  45,
  48,
  52,
  55,
  57,
  220,
  230,
  252,
  259,
  260,
  265,
  276,
  354,
  359,
  364,
  366,
  369,
  370,
  384,
  385,
  448,
  503,
  507,
  527,
  534,
  537,
  545,
  551,
  563,
  571,
  580,
  581,
  582,
  583,
  584,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 43 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 43 → SparsePoly (Fin 59) := ![
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (22, 1), (30, 1), (55, 2)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (27, 1), (30, 1), (55, 2)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (32, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (30, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (35, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (22, 1), (30, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (22, 1), (30, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (27, 1), (30, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (41, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (44, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (46, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (25, 1), (27, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (25, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (25, 1), (35, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (23, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (23, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (25, 1), (27, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (27, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (32, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (35, 1), (44, 1), (49, 1), (50, 1)] }, { coefficient := -2, powers := [(7, 1), (22, 1), (23, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (35, 1), (41, 1), (44, 1), (50, 1)] }, { coefficient := -2, powers := [(11, 1), (22, 1), (23, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (23, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (27, 1), (44, 2), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (14, 1), (23, 1), (27, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (23, 1), (32, 1), (52, 2)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (23, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (22, 1), (33, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (22, 1), (33, 1), (52, 2)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (22, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (22, 1), (23, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (23, 1), (35, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (14, 1), (22, 1), (23, 1), (52, 2)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (22, 1), (23, 1), (52, 2)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (23, 1), (27, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (18, 1), (33, 1), (44, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (22, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (22, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (44, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (35, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (35, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (27, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (35, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (30, 1), (35, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (30, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (23, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (23, 1), (35, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (23, 1), (27, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (23, 1), (32, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (23, 1), (35, 1), (44, 1), (49, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (22, 1), (23, 1), (44, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (23, 1), (35, 1), (41, 1), (44, 1)] }, { coefficient := 2, powers := [(11, 1), (19, 1), (22, 1), (23, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(16, 1), (19, 1), (22, 1), (23, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(16, 1), (19, 1), (23, 1), (27, 1), (44, 2)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (23, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (27, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (35, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (19, 1), (23, 1), (27, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (23, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (23, 1), (35, 1), (49, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (22, 1), (23, 1), (55, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (23, 1), (35, 1), (41, 1)] }, { coefficient := -2, powers := [(11, 1), (19, 1), (22, 1), (23, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (22, 1), (23, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (23, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (22, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (27, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (35, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (22, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (22, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (27, 1), (44, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (27, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (32, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (23, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (23, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (44, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (38, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (35, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (27, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (35, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (30, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (14, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (14, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (14, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (27, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (16, 1), (22, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (23, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (44, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (44, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (33, 1), (52, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (16, 1), (22, 1), (23, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (27, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (30, 1), (35, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (22, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (30, 1), (35, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (23, 1), (35, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (23, 1), (35, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (39, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (39, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (39, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (39, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (38, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (16, 1), (22, 1), (52, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (22, 1), (29, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (27, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (32, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (22, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (22, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (35, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (22, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (27, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (35, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (32, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (27, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (30, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (30, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (35, 1), (36, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (22, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (27, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (35, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (22, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (30, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (22, 1), (28, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (22, 1), (30, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (30, 1), (35, 1), (38, 1)] }]
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
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 43,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB4_2.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB4_2
