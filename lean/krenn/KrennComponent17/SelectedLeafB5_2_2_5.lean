import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_2_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bfbd5830e7d31f3d62d13b546873e490794b17db21f46e91ecceeb9e4a0b0ac6"
def certificateSHA256 : String := "0dfbd9b696b9e5cbd90fa6df27a7b81af68b075b5a402964e7f010a23594665a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 56 → Fin 614 := ![
  5,
  7,
  12,
  14,
  17,
  18,
  21,
  26,
  32,
  40,
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
  311,
  312,
  323,
  325,
  326,
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
  549,
  557,
  567,
  568,
  573,
  599,
  601,
  602,
  604,
  605,
  607,
  608,
  610,
  611,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 56 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
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
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
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
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 56 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (27, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (48, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -4, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (27, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (27, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (27, 1), (30, 1), (36, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (23, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (28, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(22, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (43, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (43, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (43, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (40, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (28, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (24, 1), (40, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (24, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (24, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 4, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (30, 1), (36, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (24, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (18, 1), (23, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (24, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (24, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (24, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (23, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (23, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (28, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (24, 1), (43, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (24, 1), (43, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (43, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -4, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (42, 1), (52, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (36, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (30, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (18, 1), (23, 1), (33, 1), (52, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (23, 1), (39, 1), (52, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (19, 1), (23, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (18, 1), (23, 1), (30, 1), (52, 1)] }, { coefficient := -4, powers := [(9, 1), (17, 1), (18, 1), (22, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (19, 1), (23, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (19, 1), (22, 1), (23, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (19, 1), (22, 1), (23, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (22, 1), (23, 1), (30, 1), (36, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (28, 1), (46, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 56,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_2_2_5.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_2_2_5
