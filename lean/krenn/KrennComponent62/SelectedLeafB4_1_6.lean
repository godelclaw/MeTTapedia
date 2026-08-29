import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4c2f20c900698387a0f9fb8efb6ea4651ec5f137e3b85133ef9a6ae207a7e164"
def certificateSHA256 : String := "adaaad5020a917eacc5748a319bb0ae0d3654c1c020e2525afe2b5b606091854"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 43 → Fin 667 := ![
  6,
  7,
  16,
  18,
  21,
  22,
  23,
  135,
  137,
  139,
  153,
  154,
  160,
  191,
  245,
  293,
  301,
  302,
  303,
  311,
  315,
  362,
  374,
  408,
  436,
  454,
  455,
  466,
  478,
  557,
  578,
  605,
  619,
  649,
  656,
  657,
  658,
  659,
  660,
  662,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 43 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 43 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (31, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (31, 1), (39, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (31, 1), (36, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (36, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (21, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (36, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (29, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (21, 1), (31, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (26, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (29, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (29, 1), (35, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (29, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (29, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (7, 1), (21, 1), (31, 1), (50, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (26, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (29, 1), (52, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (32, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (29, 1), (35, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (7, 1), (21, 1), (31, 1), (45, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (26, 1), (45, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (29, 1), (45, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (32, 1), (45, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (29, 1), (35, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (27, 1), (31, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (22, 1), (31, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (27, 1), (39, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (27, 1), (39, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (29, 1), (39, 1), (41, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (29, 1), (39, 1), (43, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (29, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (21, 1), (31, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (32, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (10, 1), (29, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (23, 1), (31, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (23, 1), (29, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (21, 1), (31, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (32, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (29, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (27, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (27, 1), (29, 1), (39, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (31, 1), (46, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (21, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (27, 1), (29, 1), (39, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (19, 1), (21, 1), (42, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (29, 1), (39, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (42, 1), (48, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (21, 1), (31, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (29, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (43, 1), (48, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (21, 1), (43, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (45, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (42, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (29, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (27, 1), (31, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (26, 1), (27, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (27, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (27, 1), (32, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (27, 1), (29, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (21, 1), (42, 1), (48, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (7, 1), (21, 1), (31, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (26, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (32, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (29, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (39, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (45, 1), (48, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (31, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (27, 1), (39, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (27, 1), (29, 1), (39, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (55, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (31, 1), (36, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (31, 1), (39, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (39, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (21, 1), (31, 1), (36, 1), (50, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (21, 1), (31, 1), (45, 1), (50, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (26, 1), (36, 1), (58, 2), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (26, 1), (45, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (29, 1), (36, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (29, 1), (45, 1), (52, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (32, 1), (36, 1), (50, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (32, 1), (45, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (29, 1), (35, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (29, 1), (35, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (29, 1), (35, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (29, 1), (35, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (29, 1), (35, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (21, 1), (27, 1), (31, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (26, 1), (27, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (27, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (27, 1), (32, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (10, 1), (27, 1), (29, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (21, 1), (39, 1), (50, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (21, 1), (45, 1), (48, 1), (50, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (21, 1), (50, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (21, 1), (31, 1), (39, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (21, 1), (31, 1), (45, 1), (48, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (21, 1), (31, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (18, 1), (21, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (18, 1), (27, 1), (29, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (21, 1), (23, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (23, 1), (27, 1), (29, 1), (39, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (21, 1), (23, 1), (39, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (21, 1), (23, 1), (45, 1), (48, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (21, 1), (23, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (21, 1), (23, 1), (42, 1), (48, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (21, 1), (42, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (21, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (50, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (21, 1), (30, 1), (31, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (21, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (26, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (21, 1), (22, 1), (31, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (22, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (22, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (22, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (30, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (29, 1), (30, 1), (35, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 43,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_1_6.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_1_6
