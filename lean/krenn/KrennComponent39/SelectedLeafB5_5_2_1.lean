import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_5_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bc843172aedf6d27e3893ba0b5d81a6701152626899fbc28c51aaa426065fa27"
def certificateSHA256 : String := "adf7205a8b83121d63e7c7b751f74cd9eb03a461719f49fcd758c925da770148"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 673 := ![
  192,
  277,
  300,
  301,
  319,
  321,
  324,
  396,
  397,
  410,
  411,
  416,
  422,
  430,
  439,
  441,
  457,
  460,
  465,
  482,
  580,
  604,
  608,
  633,
  644,
  649,
  660,
  661,
  663,
  665,
  666,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (49, 1), (51, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (37, 1), (49, 1), (51, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (28, 1), (51, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (40, 1), (51, 2), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (26, 1), (40, 1), (51, 2), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (26, 1), (37, 1), (40, 1), (51, 2), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (51, 2), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (31, 1), (51, 2), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (31, 1), (37, 1), (51, 2), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (40, 1), (51, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (26, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (26, 1), (37, 1), (40, 1), (51, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (31, 1), (51, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (31, 1), (37, 1), (51, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (21, 1), (35, 1), (44, 2), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (27, 1), (35, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (21, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (26, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (35, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (22, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (31, 1), (37, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (22, 1), (49, 1), (51, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (37, 1), (49, 1), (51, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (35, 1), (44, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (28, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (21, 1), (35, 1), (44, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (16, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (22, 1), (51, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (37, 1), (51, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (18, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (51, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (37, 1), (51, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (35, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(0, 2), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (35, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (35, 1), (51, 1), (59, 2)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (35, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (21, 1), (35, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (26, 1), (35, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (34, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (34, 1), (37, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (31, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (22, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (3, 1), (36, 1), (59, 2), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (21, 1), (35, 1), (39, 1), (44, 2), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (21, 1), (35, 1), (44, 3), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (27, 1), (35, 1), (39, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (27, 1), (35, 1), (44, 2), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (36, 1), (39, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (36, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (36, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (47, 1), (51, 2), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (39, 1), (42, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (36, 1), (59, 2)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (31, 1), (47, 1), (51, 2), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (22, 1), (39, 1), (42, 1), (49, 1), (51, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (40, 1), (42, 1), (51, 2), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (31, 1), (37, 1), (47, 1), (51, 2), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (21, 1), (39, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (21, 1), (44, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (22, 1), (45, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (26, 1), (39, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (26, 1), (44, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (16, 1), (28, 1), (47, 1), (51, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (31, 1), (37, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (22, 1), (39, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (31, 1), (37, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (26, 1), (40, 1), (42, 1), (51, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (37, 1), (39, 1), (42, 1), (49, 1), (51, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (26, 1), (37, 1), (40, 1), (42, 1), (51, 2), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (35, 1), (39, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (35, 1), (44, 2), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (35, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (35, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (39, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1), (64, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_5_2_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_5_2_1
