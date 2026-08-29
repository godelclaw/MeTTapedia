import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8fadef82391967f7716b8b030588c22ba2112ca3df09395d04dc90f48835c7ae"
def certificateSHA256 : String := "e829b06f34f99587bbd0484210ad70e0bc10a5f59046f926eeabae8b68bea99a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 55 → Fin 614 := ![
  5,
  7,
  12,
  14,
  17,
  18,
  21,
  26,
  32,
  183,
  190,
  206,
  207,
  208,
  210,
  211,
  214,
  306,
  307,
  310,
  312,
  323,
  325,
  329,
  330,
  334,
  414,
  415,
  423,
  430,
  432,
  434,
  441,
  445,
  459,
  468,
  469,
  481,
  541,
  549,
  553,
  557,
  567,
  568,
  573,
  599,
  601,
  602,
  604,
  606,
  607,
  608,
  610,
  611,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 55 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 55 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (27, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (27, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (36, 1), (38, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 2), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (23, 1), (24, 2), (27, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (27, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (27, 1), (44, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (27, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 2), (27, 1), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (27, 1), (30, 1), (36, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (27, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (27, 1), (30, 1), (36, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (42, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (28, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(22, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (43, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (40, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (18, 1), (23, 1), (24, 2), (44, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (44, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 2), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (30, 1), (36, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (30, 1), (36, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 2), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (39, 1), (44, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (39, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (24, 2), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (28, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (43, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (23, 1), (24, 2), (42, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (36, 1), (44, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (36, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 2), (39, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (30, 1), (36, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (39, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (30, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (23, 1), (24, 1), (33, 1), (39, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (23, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (23, 1), (24, 2), (39, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (23, 1), (24, 1), (39, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (24, 1), (39, 1), (40, 1), (44, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (24, 1), (39, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (39, 1), (40, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (19, 1), (23, 1), (24, 1), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (19, 1), (23, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (24, 1), (30, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (30, 1), (52, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (18, 1), (22, 1), (23, 1), (24, 2), (44, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (18, 1), (22, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (23, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (23, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (19, 1), (22, 1), (23, 1), (24, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (19, 1), (22, 1), (23, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (19, 1), (22, 1), (23, 1), (24, 1), (44, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (19, 1), (22, 1), (23, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (23, 1), (24, 2), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (23, 1), (24, 1), (30, 1), (36, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (23, 1), (24, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (23, 1), (30, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (39, 1), (44, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (39, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (35, 1), (36, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (41, 1), (44, 1)] }]
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
    ¬ ∀ index : Fin 55,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_2_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_2_4
