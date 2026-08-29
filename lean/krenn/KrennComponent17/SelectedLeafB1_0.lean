import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB1_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "84f50944c9134df37a0009e1a49f4eda15aaee4dafc07262286d6a8ad0a3a98b"
def certificateSHA256 : String := "300c29c0367e562bc873900f019bdac3789f8bdd165d250aab08d1eb0eb34ed5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 43 → Fin 608 := ![
  5,
  7,
  14,
  17,
  18,
  26,
  27,
  32,
  190,
  206,
  214,
  215,
  311,
  312,
  325,
  410,
  411,
  427,
  432,
  434,
  436,
  441,
  445,
  468,
  484,
  486,
  505,
  541,
  549,
  550,
  553,
  567,
  568,
  572,
  573,
  593,
  599,
  601,
  602,
  604,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 43 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 43 → SparsePoly (Fin 60) := ![
  [{ coefficient := -2, powers := [(2, 2), (38, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (5, 1), (29, 1), (36, 1), (57, 2), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (23, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (29, 1), (36, 1), (44, 1), (47, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (22, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (27, 1), (38, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (23, 1), (25, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (25, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 4, powers := [(9, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := 4, powers := [(9, 1), (24, 1), (27, 1), (59, 1)] }, { coefficient := 2, powers := [(19, 1), (22, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(19, 1), (27, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(22, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(27, 1), (30, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (22, 1), (30, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (27, 1), (30, 1), (59, 1)] }, { coefficient := -2, powers := [(9, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := -2, powers := [(9, 1), (24, 1), (27, 1), (59, 1)] }, { coefficient := 2, powers := [(22, 1), (24, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(22, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(24, 1), (27, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(27, 1), (30, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (17, 1), (47, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (36, 1), (47, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (8, 1), (47, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (22, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (27, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(22, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(22, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(28, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 2), (36, 1), (47, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (5, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (18, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (35, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (5, 1), (27, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (6, 1), (29, 1), (36, 1), (57, 2), (59, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (18, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (59, 2)] }, { coefficient := 1, powers := [(2, 1), (27, 1), (59, 2)] }, { coefficient := 1, powers := [(22, 1), (59, 1)] }, { coefficient := 2, powers := [(24, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (22, 1), (59, 1)] }, { coefficient := -2, powers := [(9, 1), (27, 1), (59, 1)] }, { coefficient := -2, powers := [(22, 1), (24, 1), (49, 1), (59, 1)] }, { coefficient := 2, powers := [(22, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(24, 1), (27, 1), (49, 1), (59, 1)] }, { coefficient := 2, powers := [(27, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (59, 2)] }, { coefficient := 1, powers := [(19, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (59, 2)] }, { coefficient := 1, powers := [(19, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (47, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (36, 1), (47, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (13, 1), (38, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (23, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (27, 1), (59, 2)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (59, 2)] }, { coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (5, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (8, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (13, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (13, 1), (29, 1), (36, 1), (47, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 2), (59, 2)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1), (24, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (27, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (30, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (24, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (27, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (13, 1), (23, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (19, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (19, 1), (37, 1), (57, 1), (59, 2)] }, { coefficient := 1, powers := [(2, 2), (19, 1), (44, 1), (50, 1), (59, 2)] }, { coefficient := 2, powers := [(2, 2), (36, 1), (44, 1), (47, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 2), (50, 1), (59, 2)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (5, 1), (35, 1), (44, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (18, 1), (23, 1), (44, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (27, 1), (45, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (35, 1), (36, 1), (44, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (13, 1), (23, 1), (36, 1), (45, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (13, 1), (29, 1), (36, 1), (44, 1), (47, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (44, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (36, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (42, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (28, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (36, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (42, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (59, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (17, 1), (22, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (27, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (22, 1), (33, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (27, 1), (33, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (24, 1), (42, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (27, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 2), (19, 1), (54, 1), (59, 2)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (13, 1), (23, 1), (36, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (19, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (22, 1), (24, 1), (48, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (22, 1), (30, 1), (36, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (24, 1), (27, 1), (48, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (27, 1), (30, 1), (36, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 2), (19, 1), (59, 2)] }, { coefficient := 2, powers := [(2, 1), (13, 1), (23, 1), (25, 1), (36, 1), (43, 1), (57, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (13, 1), (24, 1), (29, 1), (36, 1), (47, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (22, 1), (24, 1), (33, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (22, 1), (30, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (24, 1), (27, 1), (33, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (27, 1), (30, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (22, 1), (24, 2), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (22, 1), (24, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (24, 2), (27, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (24, 1), (27, 1), (30, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 2), (3, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (8, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (8, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (6, 1), (18, 1), (29, 1), (36, 1), (57, 2), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (27, 1), (43, 1), (57, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 43,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB1_0.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB1_0
