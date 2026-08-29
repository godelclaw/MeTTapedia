import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1906652e8edade5c50b09f165a8acd012a68d0f97e46f7d8e65bec712aa90495"
def certificateSHA256 : String := "c75473217f93e744acb0499199a0ead2b4c897d81255131f6976722c811b1043"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 611 := ![
  5,
  6,
  7,
  17,
  18,
  30,
  32,
  37,
  190,
  206,
  207,
  214,
  281,
  300,
  306,
  309,
  311,
  323,
  325,
  330,
  414,
  415,
  425,
  427,
  432,
  434,
  441,
  445,
  446,
  454,
  468,
  469,
  480,
  481,
  501,
  549,
  550,
  569,
  570,
  571,
  593,
  595,
  600,
  601,
  602,
  603,
  604,
  607,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (43, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (35, 1), (43, 1), (52, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (11, 1), (17, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (17, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (43, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (40, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (35, 1), (52, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (25, 1), (44, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1), (23, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (27, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (43, 1), (44, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (22, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 2), (32, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (19, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (44, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (35, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (11, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (25, 1), (43, 1), (44, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (43, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (37, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (19, 1), (23, 1), (24, 1), (40, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (19, 1), (23, 1), (24, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (26, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (26, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (21, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (35, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 2), (32, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (25, 1), (43, 1), (44, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (44, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_2_1.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_2_1
