import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5a8ec16a9a9698e36cd456bac171a848fd72139cacad0c29e42ed6aec0ae12b9"
def certificateSHA256 : String := "945914b780ee6b7eb1a595b89642d612dde605ab833817704db47e9ef4065f7a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 63 → Fin 673 := ![
  10,
  11,
  14,
  23,
  26,
  27,
  170,
  175,
  180,
  181,
  187,
  190,
  191,
  192,
  193,
  196,
  197,
  254,
  277,
  300,
  301,
  302,
  303,
  304,
  305,
  318,
  322,
  345,
  360,
  363,
  365,
  367,
  372,
  425,
  430,
  434,
  440,
  441,
  463,
  467,
  468,
  470,
  482,
  503,
  520,
  529,
  535,
  542,
  566,
  568,
  580,
  581,
  603,
  659,
  660,
  661,
  662,
  663,
  666,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 63 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 63 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (27, 1), (28, 1), (45, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (27, 1), (31, 1), (45, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (26, 1), (30, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (31, 1), (34, 1), (37, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (31, 1), (34, 1), (37, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (7, 1), (16, 1), (31, 1), (34, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (10, 1), (16, 1), (31, 1), (34, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (12, 1), (26, 1), (34, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (12, 1), (26, 1), (34, 1), (47, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (7, 1), (34, 2), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 2), (10, 1), (34, 2), (54, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (30, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (33, 1), (44, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (45, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (20, 1), (28, 1), (34, 1), (47, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (20, 1), (28, 1), (34, 1), (47, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (24, 1), (27, 2), (33, 1), (45, 1), (47, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(24, 1), (27, 1), (47, 1), (64, 1)] }, { coefficient := -2, powers := [(28, 1), (47, 1), (64, 1)] }, { coefficient := 2, powers := [(34, 1), (37, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (14, 1), (22, 1), (27, 1), (33, 1), (45, 2), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (27, 2), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(22, 1), (45, 1)] }, { coefficient := -2, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (20, 1), (28, 1), (34, 1), (47, 1), (49, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (20, 1), (28, 1), (34, 1), (47, 1), (49, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (22, 1), (27, 1), (33, 1), (42, 1), (45, 1), (54, 2), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (24, 1), (27, 2), (33, 1), (45, 1), (47, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (24, 1), (27, 2), (33, 1), (45, 1), (47, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (27, 2), (33, 1), (45, 1), (47, 1), (54, 2)] }, { coefficient := -2, powers := [(22, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(24, 1), (27, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := -2, powers := [(24, 1), (27, 1), (47, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(28, 1), (47, 1), (49, 1), (64, 1)] }, { coefficient := -2, powers := [(34, 1), (37, 1), (49, 1), (61, 1)] }, { coefficient := -2, powers := [(34, 1), (37, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (33, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (33, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (16, 1), (18, 1), (27, 1), (33, 1), (44, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (44, 1), (47, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (44, 1), (46, 1)] }, { coefficient := -4, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (12, 1), (20, 1), (34, 1), (53, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (34, 1), (53, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (27, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (14, 1), (16, 1), (27, 1), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (47, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (16, 1), (23, 1), (27, 1), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (46, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (17, 1), (27, 1), (31, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (27, 1), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (20, 1), (28, 1), (34, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (20, 1), (28, 1), (34, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (16, 1), (22, 1), (27, 1), (33, 1), (45, 1), (54, 2), (61, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (16, 1), (20, 1), (28, 1), (34, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (16, 1), (20, 1), (28, 1), (34, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (16, 1), (24, 1), (27, 2), (33, 1), (45, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (16, 1), (27, 1), (28, 1), (33, 1), (44, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (44, 1), (47, 1)] }, { coefficient := 2, powers := [(16, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (16, 1), (21, 1), (27, 1), (33, 1), (44, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (16, 1), (22, 1), (27, 1), (33, 1), (45, 2), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (16, 1), (27, 2), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (44, 1), (47, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1)] }, { coefficient := -2, powers := [(17, 1), (21, 1), (44, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (26, 1), (46, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (26, 1), (46, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1), (23, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (16, 1), (21, 1), (27, 1), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (47, 1)] }, { coefficient := 2, powers := [(17, 1), (21, 1), (46, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (24, 1), (27, 1), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (14, 1), (27, 1), (31, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (27, 1), (34, 1), (45, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (22, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (22, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (27, 1), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (20, 1), (28, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (20, 1), (28, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(28, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (22, 1), (27, 1), (33, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(22, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (17, 1), (44, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (44, 1)] }, { coefficient := 4, powers := [(17, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (14, 1), (16, 1), (22, 1), (27, 1), (33, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (26, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (26, 1), (51, 1)] }, { coefficient := -2, powers := [(17, 1), (26, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (16, 1), (20, 1), (28, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (16, 1), (20, 1), (28, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (27, 1), (33, 1), (45, 1), (47, 1), (54, 2)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (8, 1), (31, 1), (34, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (10, 1), (31, 1), (34, 1), (47, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (44, 1), (53, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (6, 1), (7, 1), (31, 1), (34, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (10, 1), (31, 1), (34, 1), (47, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (12, 1), (20, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (14, 1), (33, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (26, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (20, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (27, 1), (33, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(5, 1), (14, 1), (16, 1), (22, 1), (27, 1), (33, 1), (42, 1), (45, 1), (54, 2)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (16, 1), (24, 1), (27, 2), (33, 1), (45, 1), (47, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := -2, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (49, 1)] }, { coefficient := -2, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (44, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (20, 1), (34, 1), (37, 1), (54, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (20, 1), (34, 1), (47, 1), (54, 2), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (37, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (47, 1), (54, 2), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (24, 1), (27, 1), (33, 1), (44, 1), (45, 1), (47, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (27, 1), (33, 1), (35, 1), (45, 1), (47, 1), (54, 2), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (27, 1), (33, 1), (37, 1), (45, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (27, 1), (33, 1), (45, 1), (47, 1), (54, 2)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(35, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (17, 1), (28, 1), (44, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (8, 1), (20, 1), (34, 2), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (16, 1), (20, 1), (28, 1), (34, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (10, 1), (20, 1), (34, 2), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (16, 1), (20, 1), (28, 1), (34, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (17, 1), (27, 1), (28, 1), (33, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (28, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1)] }, { coefficient := 2, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (26, 1), (44, 1), (53, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (28, 1), (39, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (28, 1), (44, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (26, 1), (44, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (26, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (26, 1), (56, 1)] }, { coefficient := -4, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (7, 1), (20, 1), (34, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (10, 1), (20, 1), (34, 1), (40, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (14, 1), (27, 1), (33, 1), (40, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(2, 1), (40, 1)] }, { coefficient := 2, powers := [(5, 2), (7, 1), (20, 1), (31, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 2), (10, 1), (20, 1), (31, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 2), (14, 1), (27, 1), (30, 1), (31, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 2), (14, 1), (27, 1), (31, 1), (33, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (12, 1), (20, 1), (22, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (22, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (16, 1), (22, 1), (27, 1), (33, 1), (45, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (12, 1), (20, 1), (28, 1), (34, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (16, 1), (20, 1), (28, 1), (34, 1), (47, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (28, 1), (34, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (16, 1), (20, 1), (28, 1), (34, 1), (47, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (12, 1), (14, 1), (24, 1), (27, 2), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (16, 1), (24, 1), (27, 2), (33, 1), (45, 1), (47, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (27, 1), (47, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -2, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (49, 1)] }, { coefficient := -2, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := 2, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (5, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (39, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (27, 1), (46, 1), (54, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 63,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_2_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_2_5
