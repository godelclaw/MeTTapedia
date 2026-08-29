import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "76348b3f2f41ccba5d6e768ac0aad73a4d7118dc4904336c64a35bc71d211063"
def certificateSHA256 : String := "072ead26007478719b7b5d70a744f2b5c33206cb38206b70032ecc6f06b090fb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 43 → Fin 593 := ![
  2,
  3,
  8,
  11,
  13,
  24,
  27,
  32,
  33,
  38,
  40,
  44,
  208,
  210,
  219,
  222,
  243,
  245,
  246,
  252,
  272,
  287,
  363,
  368,
  374,
  376,
  377,
  459,
  478,
  499,
  537,
  548,
  549,
  567,
  569,
  573,
  585,
  586,
  587,
  588,
  589,
  591,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 43 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 43 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(5, 2), (7, 1), (23, 1), (29, 1), (32, 1), (41, 1), (54, 1), (56, 2), (61, 1)] }, { coefficient := 1, powers := [(5, 2), (7, 1), (29, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (41, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (24, 1), (27, 1), (32, 1), (41, 1), (54, 1), (56, 2), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (24, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (41, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (41, 1), (50, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (32, 1), (41, 1), (43, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (23, 1), (32, 1), (41, 1), (44, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 2), (32, 1), (34, 1), (41, 1), (44, 1), (49, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (41, 1), (50, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (41, 1), (50, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (27, 1), (32, 1), (41, 1), (50, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (32, 1), (34, 1), (41, 1), (49, 1), (50, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (24, 1), (27, 1), (32, 1), (41, 1), (43, 1), (51, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (24, 1), (32, 1), (34, 1), (41, 1), (43, 1), (49, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (23, 1), (24, 1), (32, 1), (41, 1), (43, 1), (51, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (24, 1), (32, 1), (34, 1), (41, 1), (43, 1), (49, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (43, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (41, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (32, 2), (41, 1), (46, 1), (54, 1), (56, 1), (58, 1), (61, 2)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (32, 2), (34, 1), (41, 1), (46, 1), (49, 1), (54, 1), (58, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (41, 1), (53, 1), (54, 1), (56, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (27, 1), (32, 1), (41, 1), (43, 1), (54, 1), (56, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (37, 1), (41, 1), (54, 1), (56, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (23, 1), (32, 1), (41, 1), (53, 2), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (27, 1), (32, 1), (41, 1), (43, 1), (53, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (34, 1), (37, 1), (41, 1), (53, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (23, 1), (32, 1), (41, 1), (49, 1), (53, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (41, 1), (43, 1), (49, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (34, 1), (37, 1), (41, 1), (49, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (41, 1), (46, 1), (58, 1), (61, 2)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1), (49, 2), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (12, 1), (23, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (12, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (32, 2), (41, 1), (54, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (32, 2), (34, 1), (41, 1), (49, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (41, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (24, 1), (27, 1), (32, 1), (41, 1), (43, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (24, 1), (32, 1), (34, 1), (41, 1), (43, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (19, 1), (23, 1), (24, 1), (32, 1), (41, 1), (43, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (19, 1), (24, 1), (32, 1), (34, 1), (41, 1), (43, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1), (43, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (27, 1), (32, 1), (41, 1), (51, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 2), (32, 1), (34, 1), (41, 1), (49, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (27, 1), (32, 1), (41, 2), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (32, 1), (34, 1), (41, 2), (49, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (23, 1), (32, 1), (41, 1), (54, 2), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 2), (32, 1), (34, 1), (41, 1), (49, 1), (54, 2), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (41, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (17, 1), (23, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (17, 1), (27, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (41, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (31, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (12, 1), (23, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 2), (12, 1), (27, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (19, 1), (24, 1), (27, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (19, 1), (24, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (19, 1), (23, 1), (24, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (19, 1), (24, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (7, 1), (23, 1), (32, 1), (41, 1), (54, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 2), (7, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (41, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (32, 1), (41, 1), (54, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (27, 1), (32, 1), (41, 1), (51, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (41, 1), (49, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (41, 1), (51, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (41, 1), (49, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(41, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (41, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (34, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (29, 1), (41, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(29, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (27, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (19, 1), (23, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (19, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (14, 1), (27, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (14, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (14, 1), (23, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (14, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (34, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (41, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (32, 1), (41, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (34, 1), (37, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (25, 1), (32, 1), (41, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (41, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (34, 1), (37, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (27, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 2), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (23, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (27, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (32, 2), (41, 1), (46, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (32, 2), (34, 1), (41, 1), (46, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (41, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (41, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (41, 1), (43, 1), (49, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (27, 1), (32, 1), (38, 1), (41, 1), (54, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (27, 1), (32, 1), (41, 2), (54, 2), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (38, 1), (41, 1), (49, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (41, 2), (49, 1), (54, 2), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (38, 1), (41, 1), (54, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (41, 2), (54, 2), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (38, 1), (41, 1), (49, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (41, 2), (49, 1), (54, 2), (61, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(41, 2), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (25, 1), (27, 1), (32, 2), (41, 1), (46, 1), (54, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (25, 1), (32, 2), (34, 1), (41, 1), (46, 1), (49, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (25, 1), (32, 1), (41, 1), (53, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (27, 1), (32, 1), (41, 1), (43, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (32, 1), (34, 1), (37, 1), (41, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (25, 1), (32, 1), (41, 1), (53, 2), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (25, 1), (27, 1), (32, 1), (41, 1), (43, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (25, 1), (32, 1), (34, 1), (37, 1), (41, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (25, 1), (32, 1), (41, 1), (49, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (25, 1), (27, 1), (32, 1), (41, 1), (43, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (25, 1), (32, 1), (34, 1), (37, 1), (41, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (41, 1), (46, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (29, 1), (41, 1), (49, 2), (60, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 43,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB4_7
