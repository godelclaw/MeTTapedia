import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_2_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a7f8a9577abbb8eca23c2371db6cf5e2eddc2cb0b7611cf534b20450538adbf8"
def certificateSHA256 : String := "704bba21883340f254f7913ccfa00972bcf0f64f7078465d5322527b804681aa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 673 := ![
  180,
  187,
  189,
  191,
  193,
  313,
  316,
  317,
  318,
  322,
  345,
  367,
  413,
  416,
  417,
  418,
  419,
  425,
  429,
  439,
  440,
  445,
  467,
  497,
  522,
  535,
  555,
  566,
  570,
  581,
  615,
  651,
  660,
  661,
  663,
  666,
  668,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(19, 1), (27, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (49, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (42, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (18, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (42, 1), (57, 1), (60, 1), (64, 2)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (42, 1), (57, 1), (60, 1), (64, 2)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (46, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (42, 1), (52, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (42, 1), (54, 1), (57, 1), (64, 2)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (42, 1), (46, 1), (49, 1), (57, 1), (64, 2)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (46, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (27, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (18, 1), (27, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (44, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (57, 1), (60, 1), (64, 2)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (57, 1), (60, 1), (64, 2)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (46, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (52, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1), (57, 1), (64, 2)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (46, 1), (49, 1), (57, 1), (64, 2)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (27, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (27, 1), (37, 1), (57, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (27, 1), (46, 1), (53, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (53, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (27, 1), (46, 1), (51, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (27, 1), (51, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (51, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (57, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (46, 1), (53, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(37, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 2), (64, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (26, 1), (44, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (27, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (27, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (27, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (27, 1), (46, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (57, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (39, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (44, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (42, 1), (44, 1), (57, 1), (60, 1), (64, 2)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (45, 1), (57, 1), (60, 1), (64, 2)] }, { coefficient := 1, powers := [(5, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (42, 1), (44, 1), (57, 1), (60, 1), (64, 2)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (45, 1), (57, 1), (60, 1), (64, 2)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (42, 1), (44, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (45, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (42, 1), (44, 1), (46, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1), (46, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (47, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (42, 1), (44, 1), (52, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (45, 1), (52, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (42, 1), (44, 1), (54, 1), (57, 1), (64, 2)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (45, 1), (54, 1), (57, 1), (64, 2)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (42, 1), (44, 1), (46, 1), (49, 1), (57, 1), (64, 2)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (45, 1), (46, 1), (49, 1), (57, 1), (64, 2)] }, { coefficient := -1, powers := [(17, 1), (46, 1), (49, 1), (57, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_2_7_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_2_7_4
