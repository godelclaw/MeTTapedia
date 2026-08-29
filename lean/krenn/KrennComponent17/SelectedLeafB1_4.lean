import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "06cbe84b4209aff398fc8a5f3d4e3f05001dd9967683b459cc172a05a674bc0c"
def certificateSHA256 : String := "0947d7b8cacdd9134047159ef7fcbc0de04ad3bdaee30f2d7b55dacdcf162d42"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 608 := ![
  5,
  7,
  14,
  18,
  32,
  41,
  190,
  202,
  206,
  209,
  214,
  281,
  306,
  311,
  323,
  324,
  325,
  330,
  353,
  410,
  425,
  427,
  432,
  434,
  438,
  441,
  445,
  453,
  454,
  456,
  459,
  462,
  470,
  481,
  484,
  505,
  544,
  549,
  550,
  554,
  558,
  571,
  572,
  593,
  601,
  602,
  604,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := -1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 61) := ![
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (29, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (19, 1), (23, 1), (25, 1), (30, 1), (32, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (19, 1), (28, 1), (30, 1), (32, 1), (38, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (25, 1), (54, 1)] }, { coefficient := -2, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 2), (19, 1), (30, 1), (32, 1), (55, 2), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (8, 1), (19, 1), (30, 1), (32, 1), (47, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (18, 1), (19, 1), (30, 1), (32, 1), (38, 1), (55, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (19, 1), (32, 1), (51, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (5, 1), (19, 1), (30, 1), (32, 1), (37, 1), (47, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (47, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 2), (19, 1), (30, 1), (32, 1), (35, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (18, 1), (19, 1), (23, 1), (30, 1), (32, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (35, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (54, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (50, 2), (51, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (50, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (19, 1), (29, 1), (30, 1), (32, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 3, powers := [(6, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(24, 1), (29, 1), (54, 1)] }, { coefficient := 2, powers := [(29, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (19, 1), (22, 1), (32, 1), (51, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (18, 1), (19, 1), (30, 1), (32, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (54, 1)] }, { coefficient := 2, powers := [(18, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (50, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (51, 1), (54, 1)] }, { coefficient := -4, powers := [(5, 1), (32, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (6, 1), (19, 1), (32, 1), (51, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (9, 1), (19, 1), (28, 1), (32, 1), (55, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (28, 1), (32, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (32, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (9, 1), (19, 1), (32, 1), (55, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (19, 1), (23, 1), (30, 1), (32, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (54, 1)] }, { coefficient := 2, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (32, 1), (51, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (32, 1), (49, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (6, 1), (19, 1), (32, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (50, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (19, 1), (30, 1), (32, 1), (38, 1), (55, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (9, 1), (17, 1), (19, 1), (32, 1), (55, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (17, 1), (19, 1), (32, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (32, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (9, 1), (17, 1), (19, 1), (28, 1), (32, 1), (55, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (17, 1), (19, 1), (28, 1), (32, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (19, 1), (32, 1), (55, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (9, 1), (32, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (32, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (50, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (54, 1)] }, { coefficient := 4, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (9, 1), (19, 1), (32, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (25, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (19, 1), (30, 1), (32, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (54, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (5, 1), (19, 1), (30, 1), (32, 1), (37, 1), (44, 1), (47, 1), (52, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (6, 1), (19, 1), (32, 1), (45, 1), (50, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (44, 1), (47, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (37, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (44, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (44, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (44, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 2), (19, 1), (30, 1), (32, 1), (35, 1), (37, 1), (44, 1), (52, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (9, 1), (17, 1), (19, 1), (28, 1), (32, 1), (50, 1), (55, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (9, 1), (19, 1), (32, 1), (37, 1), (55, 1), (57, 2), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (9, 1), (19, 1), (32, 1), (44, 1), (50, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (9, 1), (32, 1), (45, 1), (51, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (18, 1), (19, 1), (23, 1), (30, 1), (32, 1), (37, 1), (44, 1), (52, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (19, 1), (32, 1), (44, 1), (49, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (25, 1), (32, 1), (45, 1), (49, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (32, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (17, 1), (19, 1), (28, 1), (32, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (37, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (44, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (45, 1), (50, 2), (51, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (45, 1), (50, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (25, 1), (32, 1), (37, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (25, 1), (32, 1), (44, 1), (45, 1), (50, 1)] }, { coefficient := -4, powers := [(5, 1), (19, 1), (32, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (45, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (36, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (43, 1), (50, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (23, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1), (44, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (32, 1), (36, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (9, 1), (19, 1), (32, 1), (50, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (19, 1), (32, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (32, 1), (43, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (19, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (19, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (9, 1), (19, 1), (32, 1), (54, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (9, 1), (32, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (19, 1), (24, 1), (32, 1), (45, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (19, 1), (25, 1), (32, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (19, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (19, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := -4, powers := [(0, 1), (5, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (19, 1), (23, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (6, 1), (19, 1), (32, 1), (43, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (9, 1), (19, 1), (32, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (9, 1), (25, 1), (32, 1), (43, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (25, 1), (32, 1), (43, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (18, 1), (19, 1), (22, 1), (32, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (43, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (43, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (25, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (25, 1), (32, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (32, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (5, 1), (19, 1), (30, 1), (32, 1), (37, 1), (55, 2), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (55, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (8, 1), (19, 1), (30, 1), (32, 1), (35, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (18, 1), (19, 1), (29, 1), (30, 1), (32, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -3, powers := [(6, 1), (18, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (43, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (54, 1)] }, { coefficient := -2, powers := [(18, 1), (29, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB1_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB1_4
