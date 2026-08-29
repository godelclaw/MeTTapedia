import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_7_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0b4299dc9d1ae1feab5ead31bbc6d5cae75ee85a35f97e558333969c5c86f1bd"
def certificateSHA256 : String := "4290dc5f9feb85736bf7ebec9b1422ea552e1123533267a28d1a14821995b6b6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 55 → Fin 673 := ![
  179,
  180,
  187,
  189,
  190,
  191,
  192,
  195,
  196,
  219,
  251,
  277,
  282,
  301,
  308,
  311,
  317,
  318,
  321,
  322,
  324,
  394,
  396,
  398,
  416,
  419,
  424,
  425,
  434,
  439,
  440,
  457,
  462,
  467,
  468,
  471,
  482,
  521,
  566,
  567,
  570,
  589,
  608,
  644,
  650,
  660,
  661,
  663,
  664,
  665,
  666,
  668,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 55 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(11, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 55 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(27, 1), (40, 1), (42, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (47, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (47, 1), (49, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1), (48, 1), (53, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (47, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1), (53, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (40, 1), (45, 1), (53, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (40, 1), (53, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (40, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (23, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (40, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (23, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(26, 1), (47, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (19, 1), (28, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (45, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (36, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (39, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (49, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (47, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(35, 1), (40, 1), (45, 1), (53, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(40, 1), (42, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(40, 1), (45, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(44, 1), (47, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1), (40, 1), (45, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (27, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (23, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (27, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (40, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -2, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (40, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (39, 1), (40, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1), (44, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 55,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_7_2_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_7_2_5
