import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_2_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "93e52427bb6c906f91dc1d3069f7b5595a9617db7392b3960e2676a46b06ad09"
def certificateSHA256 : String := "d4c8dc9b8376bdae99d575a146401bfe483e79678ddc9997fc84e9cb4f5d1d5e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 673 := ![
  180,
  181,
  183,
  184,
  187,
  192,
  193,
  195,
  196,
  251,
  276,
  277,
  282,
  300,
  301,
  303,
  317,
  319,
  321,
  322,
  347,
  396,
  418,
  419,
  429,
  433,
  434,
  439,
  440,
  441,
  444,
  458,
  465,
  467,
  470,
  471,
  482,
  505,
  521,
  532,
  566,
  580,
  581,
  615,
  618,
  644,
  645,
  660,
  661,
  663,
  666,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (27, 1), (35, 1), (45, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (35, 1), (45, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (35, 1), (45, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (35, 1), (47, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (27, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (26, 1), (35, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (19, 1), (26, 1), (28, 1), (35, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (21, 1), (24, 1), (26, 1), (35, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (27, 1), (35, 1), (45, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (35, 1), (45, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (35, 1), (45, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (35, 1), (53, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (19, 1), (24, 1), (35, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (18, 1), (19, 1), (28, 1), (35, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (19, 1), (21, 1), (24, 1), (35, 1), (59, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (23, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (27, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(22, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (27, 1), (35, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (35, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (35, 1), (52, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (35, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (35, 1), (52, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (35, 1), (51, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (27, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (35, 1), (53, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (28, 1), (35, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (24, 1), (35, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (35, 1), (54, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1), (35, 1), (47, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (35, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (24, 1), (27, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (23, 1), (27, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (35, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (19, 1), (28, 1), (35, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (21, 1), (24, 1), (35, 1), (59, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (27, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (35, 1), (54, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 2), (27, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 2), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 2), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 2), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (19, 1), (28, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (21, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (24, 1), (27, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (23, 1), (28, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (35, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (35, 1), (36, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (35, 1), (45, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (35, 1), (47, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (37, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (40, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (47, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (35, 1), (47, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (27, 1), (35, 1), (47, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (35, 1), (47, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (19, 1), (28, 1), (35, 1), (36, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (19, 1), (28, 1), (35, 1), (45, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (28, 1), (35, 1), (47, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (21, 1), (24, 1), (35, 1), (36, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (21, 1), (24, 1), (35, 1), (45, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (23, 1), (24, 1), (27, 1), (35, 1), (36, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (23, 1), (24, 1), (27, 1), (35, 1), (45, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (28, 1), (35, 1), (36, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (28, 1), (35, 1), (45, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (24, 1), (35, 1), (47, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (24, 1), (35, 1), (36, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (24, 1), (35, 1), (45, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (35, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (35, 1), (44, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (35, 1), (37, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (35, 1), (40, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (35, 1), (46, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (35, 1), (47, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (35, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (23, 1), (27, 1), (35, 1), (44, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (24, 1), (27, 1), (35, 1), (44, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (35, 1), (44, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (23, 1), (35, 1), (44, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (24, 1), (35, 1), (44, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (35, 1), (46, 1), (49, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (35, 1), (45, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (19, 1), (28, 1), (35, 1), (45, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (21, 1), (24, 1), (35, 1), (45, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(35, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (34, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (26, 1), (35, 1), (42, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (35, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (35, 1), (40, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (26, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (23, 1), (35, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (26, 1), (35, 1), (49, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(35, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_2_6_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_2_6_5
