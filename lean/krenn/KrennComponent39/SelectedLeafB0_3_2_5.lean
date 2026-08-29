import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_3_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "136f7d2604b041d20e2a885757ba7e16ab19c49809ab0f03b9753ec6a01d7dde"
def certificateSHA256 : String := "e373d82a26ce43cd16e4f95ecf076864f5a5e3a06a932641a56f3f8b727a382a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 673 := ![
  180,
  187,
  189,
  190,
  191,
  192,
  195,
  196,
  251,
  277,
  282,
  301,
  316,
  317,
  318,
  321,
  322,
  324,
  396,
  398,
  416,
  417,
  419,
  424,
  425,
  434,
  439,
  440,
  457,
  458,
  462,
  467,
  468,
  471,
  482,
  521,
  562,
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
  665,
  666,
  668,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
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
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(28, 1), (47, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (47, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (27, 1), (40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (40, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (23, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (40, 1)] }, { coefficient := -1, powers := [(40, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (23, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(26, 1), (47, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (19, 1), (28, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (27, 1), (40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (45, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (27, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (36, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (39, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (44, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (27, 1), (36, 1), (40, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (27, 1), (39, 1), (40, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (27, 1), (40, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1), (44, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(35, 1), (40, 1), (45, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(40, 1), (42, 1), (44, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(44, 1), (47, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (27, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (23, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (27, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -2, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (39, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1), (44, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_3_2_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_3_2_5
