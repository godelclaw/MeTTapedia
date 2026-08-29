import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_1_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f7d77573bd819a535da0ea2e499004fcb8afdab589da51d9dae5b82aa2966a77"
def certificateSHA256 : String := "f961072b3b21a868dfa1300518fdb7016f0a861176b7c709df7ce50a37ce7329"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 670 := ![
  187,
  188,
  189,
  190,
  192,
  195,
  282,
  300,
  301,
  313,
  316,
  317,
  319,
  321,
  342,
  345,
  382,
  397,
  398,
  410,
  411,
  416,
  419,
  439,
  452,
  460,
  462,
  465,
  471,
  497,
  536,
  555,
  566,
  570,
  580,
  633,
  660,
  661,
  663,
  665,
  666,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (40, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (16, 1), (22, 1), (24, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (40, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (19, 1), (24, 1), (51, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (52, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (19, 1), (52, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (40, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (40, 1), (47, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (24, 1), (47, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (19, 1), (47, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (19, 1), (47, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (40, 1), (47, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (12, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (23, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (27, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (22, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (28, 1), (40, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (31, 1), (37, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (27, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (27, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (21, 1), (22, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (26, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (49, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (27, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (40, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (24, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (19, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (19, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (40, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (28, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (44, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (49, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (19, 1), (27, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (19, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (19, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (27, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (19, 1), (23, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (27, 1), (44, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (16, 1), (28, 1), (40, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (31, 1), (37, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (24, 1), (27, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (34, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (26, 1), (40, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (23, 1), (27, 1), (44, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (26, 1), (40, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (37, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (28, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (16, 1), (19, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (23, 1), (34, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (17, 1), (21, 1), (22, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (19, 1), (26, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (23, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (23, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (44, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (40, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (19, 1), (24, 1), (27, 1), (42, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (27, 1), (42, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (19, 1), (27, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (27, 1), (40, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (19, 1), (27, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (23, 1), (27, 1), (51, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_1_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_1_2
