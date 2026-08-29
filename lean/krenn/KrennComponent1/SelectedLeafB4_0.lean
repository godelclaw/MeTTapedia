import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB4_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "803892602f1bcce93eada7782c13f573e05afc243cbdd21f0ec8cf5922e9bb68"
def certificateSHA256 : String := "0e651784fa2fc01d0ad31b3c80583a89201f6175c167d88d0f5909549e542167"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 588 := ![
  3,
  13,
  15,
  25,
  35,
  37,
  38,
  39,
  48,
  52,
  55,
  218,
  230,
  245,
  255,
  260,
  261,
  266,
  275,
  330,
  354,
  364,
  366,
  369,
  370,
  382,
  384,
  385,
  456,
  493,
  503,
  507,
  511,
  545,
  546,
  556,
  558,
  571,
  580,
  581,
  583,
  584,
  586,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(5, 2), (7, 1), (27, 1), (30, 1), (33, 1), (53, 1), (55, 2)] }, { coefficient := 1, powers := [(5, 2), (7, 1), (30, 1), (33, 1), (35, 1), (49, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 2), (11, 1), (22, 1), (30, 1), (33, 1), (52, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 2), (16, 1), (22, 1), (30, 1), (33, 1), (49, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (23, 1), (27, 1), (33, 1), (45, 1), (49, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (23, 1), (33, 1), (35, 1), (45, 1), (49, 2), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (27, 1), (33, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 2), (33, 1), (35, 1), (45, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (11, 1), (33, 1), (36, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 2), (16, 1), (33, 1), (36, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (19, 1), (23, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (19, 1), (23, 1), (33, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (11, 1), (33, 2), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 2), (16, 1), (33, 2), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (14, 1), (23, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (16, 1), (23, 1), (33, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (17, 1), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 2), (17, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (12, 1), (23, 1), (27, 1), (33, 1), (49, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (12, 1), (23, 1), (33, 1), (35, 1), (49, 2), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (22, 1), (49, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (49, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (22, 1), (53, 1), (55, 2)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (52, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (27, 1), (33, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (33, 1), (35, 1), (47, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (22, 1), (49, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (22, 1), (52, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (49, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (52, 2), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (22, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (32, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (22, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (29, 1), (32, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (12, 1), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 2), (12, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 2), (7, 1), (27, 1), (33, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 2), (7, 1), (33, 1), (35, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 2), (11, 1), (22, 1), (33, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 2), (16, 1), (22, 1), (33, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 2), (7, 1), (24, 1), (27, 1), (33, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 2), (7, 1), (24, 1), (33, 1), (35, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 2), (11, 1), (22, 1), (24, 1), (33, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 2), (16, 1), (22, 1), (24, 1), (33, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (12, 1), (23, 1), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (12, 1), (23, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (32, 1), (52, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (52, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (44, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (27, 1), (33, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (47, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (33, 1), (47, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (22, 1), (33, 1), (47, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (27, 1), (30, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 2), (30, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (23, 1), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (23, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (27, 1), (30, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (22, 1), (30, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (22, 1), (30, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(30, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (23, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (19, 1), (22, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (19, 1), (22, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (14, 1), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (14, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (14, 1), (22, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (16, 1), (22, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (33, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (32, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (20, 1), (22, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (20, 1), (32, 1), (52, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (7, 1), (27, 1), (30, 1), (33, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 2), (7, 1), (30, 1), (33, 1), (35, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 2), (11, 1), (22, 1), (30, 1), (33, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 2), (16, 1), (22, 1), (30, 1), (33, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (22, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (33, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 2), (33, 1), (35, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (22, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (22, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (38, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (27, 1), (33, 1), (39, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (39, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (33, 1), (39, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (22, 1), (33, 1), (39, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 2), (7, 1), (27, 1), (30, 1), (33, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 2), (7, 1), (30, 1), (33, 1), (35, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 2), (11, 1), (22, 1), (30, 1), (33, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 2), (16, 1), (22, 1), (30, 1), (33, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (29, 1), (32, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (20, 1), (22, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (20, 1), (29, 1), (32, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (33, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (23, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (5, 1), (27, 1), (33, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (5, 1), (33, 1), (35, 1), (49, 1), (53, 2)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (11, 1), (22, 1), (33, 1), (52, 1), (53, 2)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (16, 1), (22, 1), (33, 1), (49, 1), (53, 2)] }, { coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (33, 1), (36, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (33, 1), (35, 1), (36, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (27, 1), (30, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (30, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (8, 1), (27, 1), (33, 1), (36, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (8, 1), (33, 1), (35, 1), (36, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (33, 1), (36, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (16, 1), (22, 1), (33, 1), (36, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (17, 1), (27, 1), (29, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (17, 1), (29, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (19, 1), (22, 1), (30, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (19, 1), (22, 1), (30, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }]
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
    (values : Fin 58 → R) :
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB4_0.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB4_0
