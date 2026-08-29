import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "13fa5b027ea1c689d92e951f0f832bf8ae567b0f61ebd8d9c4a4b15d769e7a15"
def certificateSHA256 : String := "27c2c0c7cb62fd0e44cafa81c8700cc16aa30a3df94768e3100afc7ef500cb01"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 79 → Fin 664 := ![
  8,
  9,
  10,
  11,
  12,
  14,
  15,
  17,
  18,
  20,
  21,
  68,
  70,
  87,
  97,
  128,
  130,
  131,
  133,
  135,
  136,
  137,
  138,
  140,
  151,
  152,
  153,
  158,
  159,
  160,
  161,
  186,
  191,
  207,
  243,
  293,
  295,
  296,
  297,
  299,
  301,
  302,
  309,
  311,
  313,
  321,
  337,
  343,
  357,
  373,
  375,
  390,
  408,
  438,
  439,
  440,
  453,
  454,
  455,
  462,
  465,
  491,
  519,
  531,
  543,
  557,
  578,
  579,
  598,
  600,
  619,
  649,
  655,
  657,
  659,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 79 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (45, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 79 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (12, 1), (20, 1), (46, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (22, 1), (25, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (25, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (22, 1), (23, 1), (25, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (13, 1), (24, 1), (25, 1), (30, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (24, 1), (25, 1), (30, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (13, 1), (23, 1), (24, 1), (25, 1), (30, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (23, 1), (24, 1), (25, 1), (30, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (25, 1), (27, 1), (31, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (25, 1), (27, 1), (28, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (25, 1), (27, 1), (48, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (22, 1), (25, 1), (31, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (22, 1), (25, 1), (28, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (22, 1), (25, 1), (48, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (24, 1), (30, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (25, 1), (27, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (25, 1), (27, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (25, 1), (27, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (18, 1), (25, 1), (27, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (20, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (20, 1), (24, 1), (33, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (24, 1), (33, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (13, 1), (20, 1), (33, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (33, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (28, 1), (33, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (20, 1), (22, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (17, 1), (20, 1), (22, 1), (28, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (18, 1), (20, 1), (22, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (17, 1), (20, 1), (22, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (17, 1), (20, 1), (22, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (20, 1), (22, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (10, 1), (12, 1), (20, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (12, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (28, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (28, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (18, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (23, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (31, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (28, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (34, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (12, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (10, 1), (17, 1), (20, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (15, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (28, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (31, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (28, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (23, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (18, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (23, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (31, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (28, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (34, 1), (45, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (13, 1), (28, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (31, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (40, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (20, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (23, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (8, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (23, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (23, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (18, 2), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (13, 1), (24, 1), (30, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (24, 1), (30, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (23, 1), (24, 1), (30, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (23, 1), (24, 1), (30, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (27, 1), (31, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (27, 1), (28, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (48, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (22, 1), (31, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (22, 1), (28, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (22, 1), (48, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (12, 1), (27, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (23, 1), (27, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (27, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (18, 1), (27, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (13, 1), (24, 1), (33, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (24, 1), (33, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (13, 1), (33, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (28, 1), (33, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (22, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (17, 1), (22, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (18, 1), (22, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (17, 1), (22, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (17, 1), (22, 1), (28, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (22, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 2), (13, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (13, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (23, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (18, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (18, 1), (28, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 2), (9, 1), (31, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (13, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (18, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (28, 1), (40, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (24, 1), (42, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (52, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (18, 2), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (48, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (13, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 2), (28, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (9, 1), (31, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (18, 1), (45, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (28, 1), (40, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (18, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (19, 1), (42, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (45, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (23, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (16, 1), (24, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (28, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (18, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (18, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (30, 1), (46, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (13, 1), (18, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (13, 1), (18, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (13, 1), (18, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (13, 1), (18, 2), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (18, 2), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (15, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (13, 1), (16, 1), (19, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (16, 1), (19, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 2), (13, 1), (16, 1), (19, 1), (28, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 2), (16, 1), (19, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (9, 1), (16, 1), (19, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (13, 1), (16, 1), (19, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (16, 1), (18, 1), (19, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (16, 1), (19, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (16, 1), (19, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (16, 1), (18, 1), (19, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (16, 1), (19, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (18, 1), (19, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (19, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 2), (9, 1), (16, 1), (19, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (13, 1), (16, 1), (19, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (16, 1), (18, 1), (19, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (16, 1), (19, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (28, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (18, 1), (23, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (27, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (27, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (22, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (22, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (22, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (13, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (9, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (13, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (18, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (9, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (13, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (18, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (28, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (30, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (23, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (13, 1), (24, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (24, 1), (30, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (15, 1), (27, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (22, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (22, 1), (23, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (10, 1), (20, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (10, 1), (20, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (18, 1), (43, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (43, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (23, 1), (38, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (23, 1), (43, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (18, 1), (27, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (22, 1), (23, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (22, 1), (23, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (18, 1), (22, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (13, 1), (24, 1), (30, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (24, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (19, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (18, 1), (20, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (18, 1), (20, 1), (53, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (30, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (22, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1), (22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (22, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (22, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (13, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (30, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (13, 1), (27, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 2), (13, 1), (27, 1), (28, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 2), (27, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (9, 1), (27, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (13, 1), (27, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (18, 1), (27, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (23, 1), (27, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (27, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (18, 1), (27, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (27, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (18, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (27, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 2), (9, 1), (27, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (13, 1), (27, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (18, 1), (27, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (27, 1), (28, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (13, 1), (19, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (19, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 2), (13, 1), (19, 1), (27, 1), (28, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 2), (19, 1), (27, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (9, 1), (19, 1), (27, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (13, 1), (19, 1), (27, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (18, 1), (19, 1), (27, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (19, 1), (23, 1), (27, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (19, 1), (27, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (18, 1), (19, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (19, 1), (27, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (18, 1), (19, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (19, 1), (27, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 2), (9, 1), (19, 1), (27, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (13, 1), (19, 1), (27, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (18, 1), (19, 1), (27, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (19, 1), (27, 1), (28, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (10, 1), (17, 1), (20, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (28, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (30, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (30, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (31, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (20, 1), (22, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (20, 1), (22, 1), (53, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (22, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (10, 1), (12, 1), (20, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (28, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (18, 1), (30, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (13, 1), (22, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (24, 1), (30, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (24, 1), (30, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (13, 1), (22, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (13, 1), (18, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 2), (13, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (13, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (18, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (9, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (13, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (18, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (28, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (27, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (10, 1), (20, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (40, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (13, 1), (24, 1), (30, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (13, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (24, 1), (30, 1), (41, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (22, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (28, 1), (33, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (22, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (27, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (27, 1), (28, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (17, 1), (22, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (18, 1), (22, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (13, 1), (23, 1), (24, 1), (30, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (24, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (23, 1), (24, 1), (30, 1), (41, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (24, 1), (33, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (27, 1), (31, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (27, 1), (28, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (34, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (17, 1), (22, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (17, 1), (22, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (22, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (22, 1), (23, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (22, 1), (31, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (22, 1), (28, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (22, 1), (34, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (18, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (13, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (19, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (9, 1), (45, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (10, 1), (20, 1), (36, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (10, 1), (20, 1), (39, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (10, 1), (20, 1), (46, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (18, 1), (43, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (40, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 2), (13, 1), (28, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 2), (28, 1), (45, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (9, 1), (31, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (13, 1), (28, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (18, 1), (45, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (23, 1), (36, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (28, 1), (40, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (18, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (19, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (45, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (18, 1), (45, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (45, 1), (52, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (18, 1), (28, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (45, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 2), (9, 1), (31, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (13, 1), (28, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (18, 1), (36, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (28, 1), (36, 1), (40, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (19, 1), (24, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (19, 1), (42, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (24, 1), (42, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (24, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (31, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (45, 1), (52, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (28, 1), (43, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (28, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 2), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (23, 1), (38, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (23, 1), (43, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (45, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(9, 1), (18, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (40, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (46, 1), (48, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (46, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (46, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (25, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (18, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (13, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (15, 1), (19, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (9, 1), (27, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (9, 1), (31, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (28, 1), (33, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (9, 1), (22, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (15, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (27, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (10, 1), (20, 1), (33, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (28, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (18, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (28, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (18, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (31, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (28, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (33, 1), (34, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 79,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB6_2.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB6_2
