import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e270cb2a94e565bb8e14f3298df7a84cecc62351bbdbae345b97f3fc9fa3d375"
def certificateSHA256 : String := "e3a15bee5e4c151c6be46917ec6c4e6a8da32361c57300e566cfaf568d09598a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 55 → Fin 667 := ![
  180,
  181,
  187,
  190,
  191,
  192,
  193,
  219,
  254,
  302,
  303,
  308,
  313,
  316,
  317,
  318,
  321,
  322,
  342,
  345,
  350,
  382,
  396,
  397,
  410,
  411,
  416,
  418,
  419,
  425,
  429,
  433,
  434,
  439,
  440,
  458,
  462,
  467,
  482,
  503,
  532,
  536,
  566,
  570,
  580,
  581,
  607,
  615,
  644,
  660,
  661,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 55 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 55 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(27, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (37, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (28, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (44, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (47, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (16, 1), (22, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (48, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (47, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1)] }, { coefficient := -1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (44, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (26, 1), (44, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (45, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (45, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (22, 1), (24, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := -1, powers := [(26, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (27, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (27, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (47, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (12, 1), (22, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (31, 1), (35, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (16, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (16, 1), (18, 1), (22, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (16, 1), (22, 1), (24, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (35, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (21, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (21, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (21, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (16, 1), (18, 1), (22, 1), (27, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (22, 1), (24, 1), (27, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (26, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (26, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (26, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (22, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (27, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (16, 1), (18, 1), (26, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (26, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (31, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (22, 1), (24, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (18, 1), (26, 1), (36, 1), (37, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (18, 1), (26, 1), (37, 1), (39, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (18, 1), (26, 1), (37, 1), (44, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (21, 1), (37, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (26, 1), (37, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (44, 1), (47, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (28, 1), (36, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (28, 1), (39, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (28, 1), (44, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (31, 1), (36, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (31, 1), (39, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (31, 1), (44, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (21, 1), (28, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (21, 1), (31, 1), (44, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (26, 1), (28, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (26, 1), (31, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (18, 1), (22, 1), (27, 1), (44, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (16, 1), (22, 1), (24, 1), (27, 1), (42, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (44, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (39, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (27, 1), (39, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (27, 1), (45, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (27, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (26, 1), (36, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (26, 1), (39, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (26, 1), (44, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (42, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (31, 1), (35, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (31, 1), (35, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (31, 1), (35, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (35, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (35, 1), (46, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (44, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (35, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (26, 1), (45, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (22, 1), (24, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (18, 1), (26, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (23, 1), (26, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (26, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (26, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (26, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (24, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (19, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (21, 1), (22, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (26, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (26, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (23, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }]
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
    ¬ ∀ index : Fin 55,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_4
