import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "daf13907e631d62bdc1064a5e7c9e2951e3f82084d5117cc6c4ff31e369d049f"
def certificateSHA256 : String := "29d50af93d5d8b7488605ef4ed25ccd7fc73798e9a86fe458ba0187795fa4399"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 617 := ![
  9,
  23,
  24,
  33,
  35,
  215,
  216,
  219,
  220,
  222,
  331,
  332,
  337,
  338,
  341,
  346,
  348,
  349,
  355,
  426,
  441,
  457,
  471,
  487,
  489,
  497,
  559,
  560,
  580,
  583,
  610,
  611,
  613,
  615,
  616
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (22, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (33, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (33, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (33, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (22, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (32, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (44, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (44, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (44, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (44, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (44, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (45, 1), (50, 1)] }, { coefficient := -2, powers := [(23, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (22, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (33, 1), (44, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (33, 1), (44, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (44, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (44, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (40, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(22, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (17, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (33, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (33, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (29, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (29, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (22, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (49, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (51, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (49, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (51, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (33, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (22, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (22, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (22, 1), (51, 1)] }, { coefficient := -2, powers := [(18, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (33, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (49, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (32, 1), (44, 1), (47, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (32, 1), (44, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (49, 2), (59, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (53, 2), (59, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (49, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (44, 1), (47, 2), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (44, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (49, 2), (59, 1)] }, { coefficient := 2, powers := [(18, 1), (47, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (53, 2), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (33, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (49, 2), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (44, 1), (47, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (44, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 2), (59, 1)] }, { coefficient := -2, powers := [(18, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (53, 2), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (47, 1), (49, 2), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (47, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (32, 1), (44, 1), (47, 2), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (32, 1), (44, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (47, 1), (49, 2), (59, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (47, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (47, 1), (53, 2), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(49, 1)] }, { coefficient := -1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(16, 1), (22, 1), (40, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (35, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (38, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (38, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (45, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (38, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (38, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(35, 1), (57, 1)] }, { coefficient := 1, powers := [(38, 1), (54, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (29, 1), (33, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (29, 1), (33, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (29, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 1), (22, 1), (33, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 1), (22, 1), (33, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (12, 1), (22, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (29, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (12, 1), (22, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (18, 1), (29, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (18, 1), (29, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (18, 1), (22, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (18, 1), (22, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (47, 1), (49, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (47, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (32, 1), (44, 1), (47, 2), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (23, 1), (32, 1), (44, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (26, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (22, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (47, 1), (49, 2), (59, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (47, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (47, 1), (53, 2), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (49, 2)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (32, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (32, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (49, 2)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 2)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component59.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB4_1
