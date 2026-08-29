import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_6_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f64a39f8b1462d7059ac24632bc6902c73362b9f33bf703d8849388015773158"
def certificateSHA256 : String := "64cff1793079184681d0cd064fefb012c94b7ebe817ec72c516edf265503e7e9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 71 → Fin 673 := ![
  17,
  180,
  181,
  183,
  184,
  187,
  192,
  195,
  196,
  251,
  270,
  276,
  277,
  282,
  300,
  301,
  303,
  304,
  305,
  316,
  318,
  319,
  321,
  322,
  347,
  396,
  397,
  416,
  417,
  419,
  422,
  434,
  439,
  440,
  441,
  444,
  457,
  465,
  470,
  471,
  476,
  505,
  511,
  513,
  515,
  521,
  532,
  566,
  571,
  580,
  581,
  590,
  602,
  603,
  614,
  618,
  644,
  645,
  649,
  659,
  660,
  661,
  662,
  663,
  664,
  666,
  668,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 71 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 71 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(21, 1), (33, 1), (36, 1), (53, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (19, 1), (24, 1), (27, 1), (33, 1), (36, 1), (45, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (28, 1), (33, 1), (36, 1), (45, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (24, 1), (33, 1), (36, 1), (45, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (34, 1), (36, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1), (33, 1), (36, 1), (47, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (19, 1), (24, 1), (27, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 2, powers := [(10, 1), (19, 1), (28, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (19, 1), (24, 1), (26, 1), (33, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (18, 1), (19, 1), (26, 1), (28, 1), (33, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (19, 1), (21, 1), (24, 1), (26, 1), (33, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (21, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (27, 1), (33, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (33, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (30, 1), (51, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (30, 1), (56, 2), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (24, 1), (27, 1), (33, 1), (36, 1), (45, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (28, 1), (33, 1), (36, 1), (45, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (24, 1), (33, 1), (36, 1), (45, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (34, 1), (36, 1), (37, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (27, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (27, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (12, 1), (23, 1), (33, 1), (36, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (17, 1), (19, 1), (24, 1), (33, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (17, 1), (18, 1), (19, 1), (28, 1), (33, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (17, 1), (19, 1), (21, 1), (24, 1), (33, 1), (36, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (17, 1), (19, 1), (23, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (24, 1), (27, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (28, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -2, powers := [(10, 1), (22, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (33, 1), (37, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (53, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (24, 1), (27, 1), (33, 1), (36, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (28, 1), (33, 1), (36, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (24, 1), (33, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (18, 1), (28, 1), (33, 1), (36, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (24, 1), (33, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (12, 1), (23, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (12, 1), (22, 1), (24, 1), (33, 1), (36, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (24, 1), (27, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (26, 1), (33, 1), (36, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (28, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (18, 1), (28, 1), (33, 1), (36, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (21, 1), (24, 1), (33, 1), (36, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (47, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (23, 1), (27, 1), (33, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (33, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (33, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (12, 1), (22, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (17, 1), (19, 1), (24, 1), (27, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (19, 1), (28, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 2, powers := [(10, 1), (17, 1), (22, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (17, 1), (19, 1), (23, 1), (27, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -2, powers := [(10, 1), (17, 1), (22, 1), (23, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (19, 1), (24, 1), (33, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (18, 1), (19, 1), (28, 1), (33, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (19, 1), (21, 1), (24, 1), (33, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (37, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (27, 1), (30, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(4, 1), (27, 1), (30, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (27, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (27, 1), (33, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (21, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (23, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (27, 1), (30, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(4, 1), (23, 1), (27, 1), (30, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (27, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (23, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (27, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (17, 1), (23, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (23, 1), (30, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (23, 1), (30, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (30, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (23, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (23, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (19, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (18, 1), (19, 1), (28, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (19, 1), (21, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (19, 1), (23, 1), (24, 1), (27, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (19, 1), (23, 1), (28, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (22, 1), (23, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (17, 1), (27, 1), (33, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (24, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (12, 1), (26, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (62, 1)] }, { coefficient := -1, powers := [(51, 1), (62, 1)] }, { coefficient := -1, powers := [(56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (30, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (20, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (33, 1), (36, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(28, 1), (33, 1), (36, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (30, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (30, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (12, 1), (23, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (17, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (27, 1), (30, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (27, 1), (30, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (27, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (27, 1), (30, 1), (36, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (27, 1), (30, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (28, 1), (66, 1)] }, { coefficient := -1, powers := [(28, 1), (30, 1), (36, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (19, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (19, 1), (24, 1), (33, 1), (36, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (19, 1), (24, 1), (33, 1), (36, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (24, 1), (33, 1), (36, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (33, 1), (36, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (33, 1), (36, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (33, 1), (36, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (27, 1), (30, 1), (44, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (27, 1), (30, 1), (44, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (27, 1), (30, 1), (51, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (39, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (33, 1), (36, 1), (47, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (24, 1), (27, 1), (33, 1), (36, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (28, 1), (33, 1), (36, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (18, 1), (19, 1), (28, 1), (33, 1), (36, 2), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (18, 1), (19, 1), (28, 1), (33, 1), (36, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (18, 1), (28, 1), (33, 1), (36, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (19, 1), (21, 1), (24, 1), (33, 1), (36, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (19, 1), (21, 1), (24, 1), (33, 1), (36, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (19, 1), (23, 1), (24, 1), (27, 1), (33, 1), (36, 2), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (19, 1), (23, 1), (24, 1), (27, 1), (33, 1), (36, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (19, 1), (23, 1), (28, 1), (33, 1), (36, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (19, 1), (23, 1), (28, 1), (33, 1), (36, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (24, 1), (33, 1), (36, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (22, 1), (23, 1), (24, 1), (33, 1), (36, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (22, 1), (23, 1), (24, 1), (33, 1), (36, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (27, 1), (30, 1), (36, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (19, 1), (23, 1), (27, 1), (33, 1), (36, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (19, 1), (24, 1), (27, 1), (33, 1), (36, 1), (44, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (19, 1), (28, 1), (33, 1), (36, 1), (44, 1), (49, 1), (65, 1)] }, { coefficient := 2, powers := [(10, 1), (17, 1), (22, 1), (23, 1), (33, 1), (36, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(10, 1), (17, 1), (22, 1), (24, 1), (33, 1), (36, 1), (44, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (27, 1), (33, 1), (37, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (46, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (20, 1), (27, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (27, 1), (30, 1), (36, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (56, 2), (62, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := 1, powers := [(50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (19, 1), (24, 1), (33, 1), (36, 1), (45, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (18, 1), (19, 1), (28, 1), (33, 1), (36, 1), (45, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (19, 1), (21, 1), (24, 1), (33, 1), (36, 1), (45, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (33, 1), (36, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (23, 1), (33, 1), (34, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (24, 1), (26, 1), (33, 1), (36, 1), (42, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (19, 1), (33, 1), (36, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (23, 1), (33, 1), (36, 1), (40, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (23, 1), (31, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (19, 1), (26, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (22, 1), (23, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (19, 1), (26, 1), (33, 1), (36, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (33, 1), (36, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (33, 1), (34, 1), (36, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (33, 1), (34, 1), (36, 1), (37, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (36, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }]
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
    ¬ ∀ index : Fin 71,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_6_2_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_6_2_5
