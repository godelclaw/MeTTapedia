import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB1_6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c4edaea47e72434283cf9963b9ed3ef694d5f7334aeba096bd3f9f99f937bd9d"
def certificateSHA256 : String := "2d498a50991aa130265dc43c76fc28750218be2b533aeaf677ee41d2d3f5757a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 611 := ![
  5,
  7,
  14,
  17,
  18,
  32,
  40,
  41,
  190,
  202,
  206,
  214,
  311,
  325,
  410,
  427,
  432,
  434,
  436,
  441,
  445,
  446,
  470,
  474,
  484,
  505,
  506,
  541,
  549,
  550,
  593,
  595,
  601,
  602,
  604,
  606,
  607,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (36, 1), (54, 1), (57, 2), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (54, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(29, 1), (36, 1), (40, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(29, 1), (36, 1), (44, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(29, 1), (40, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(29, 1), (44, 1), (47, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (38, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (51, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (54, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (23, 1), (25, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (28, 1), (38, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (8, 1), (19, 1), (47, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (19, 1), (38, 1), (57, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (40, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (44, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (40, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (44, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (19, 1), (37, 1), (47, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (19, 1), (35, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (19, 1), (23, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (35, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (29, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(6, 1), (29, 1), (36, 1), (54, 1), (57, 2), (61, 1)] }, { coefficient := 2, powers := [(6, 1), (29, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (19, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(28, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(38, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(36, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (38, 1), (54, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (23, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 2), (28, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (38, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (57, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (54, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (36, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (29, 1), (36, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (38, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (19, 1), (37, 1), (44, 1), (47, 1), (52, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (19, 1), (35, 1), (37, 1), (44, 1), (52, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (19, 1), (23, 1), (37, 1), (44, 1), (52, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (37, 1), (54, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (40, 1), (54, 2), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (44, 1), (50, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (44, 1), (47, 1), (52, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (44, 1), (52, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (23, 1), (44, 1), (52, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (44, 2), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1), (36, 1), (44, 1), (47, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (44, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (38, 1), (44, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (44, 2), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(37, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(40, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(50, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (54, 2), (61, 1)] }, { coefficient := 1, powers := [(50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (8, 1), (19, 1), (35, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (19, 1), (29, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (29, 1), (36, 1), (54, 1), (57, 2), (61, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (29, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (43, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (19, 1), (37, 1), (41, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (41, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (19, 1), (32, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (36, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (54, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB1_6_2.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB1_6_2
