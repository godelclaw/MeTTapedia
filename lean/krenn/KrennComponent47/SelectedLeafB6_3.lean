import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "939d33d3418c43d16be59143d20512fa2f30bd817c641748d0f64cd8176fe3a4"
def certificateSHA256 : String := "29c6b837119200027c470d854a65fe6cd68be9e7bdaf52b109f5287eb82e2ee5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 593 := ![
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
  250,
  272,
  287,
  363,
  366,
  368,
  374,
  376,
  377,
  390,
  459,
  478,
  499,
  537,
  548,
  549,
  567,
  569,
  573,
  576,
  585,
  586,
  587,
  589,
  591,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 62) := ![
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
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 2), (7, 1), (23, 1), (29, 1), (32, 1), (54, 1), (56, 2)] }, { coefficient := 1, powers := [(5, 2), (7, 1), (29, 1), (32, 1), (34, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (24, 1), (27, 1), (32, 1), (54, 1), (56, 2)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (32, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (23, 1), (32, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 2), (32, 1), (34, 1), (44, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (27, 1), (32, 1), (50, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (32, 1), (34, 1), (49, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (24, 1), (27, 1), (32, 1), (51, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (24, 1), (32, 1), (34, 1), (49, 1), (51, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (24, 1), (32, 1), (51, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (24, 1), (32, 1), (34, 1), (49, 1), (51, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (32, 2), (46, 1), (54, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (32, 2), (34, 1), (46, 1), (49, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (53, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (27, 1), (32, 1), (43, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (37, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (23, 1), (32, 1), (53, 2), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (27, 1), (32, 1), (43, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (34, 1), (37, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (23, 1), (32, 1), (49, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (43, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (34, 1), (37, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (46, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1), (49, 2), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (12, 1), (23, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (12, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (32, 2), (54, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (32, 2), (34, 1), (49, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (19, 1), (24, 1), (27, 1), (32, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (19, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (19, 1), (23, 1), (24, 1), (32, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (19, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (27, 1), (32, 1), (51, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 2), (32, 1), (34, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (27, 1), (32, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (23, 1), (32, 1), (54, 2), (56, 1)] }, { coefficient := -1, powers := [(5, 2), (32, 1), (34, 1), (49, 1), (54, 2)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (17, 1), (23, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (17, 1), (27, 1), (32, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (31, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (12, 1), (23, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 2), (12, 1), (27, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (31, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (31, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 2), (7, 1), (23, 1), (32, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 2), (7, 1), (32, 1), (34, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (32, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (32, 1), (34, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (27, 1), (32, 1), (51, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (51, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (24, 1), (27, 1), (32, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (24, 1), (32, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (24, 1), (27, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (23, 1), (24, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (29, 1), (41, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(29, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (27, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (19, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (19, 1), (23, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (19, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (14, 1), (27, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (14, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (14, 1), (23, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (14, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (32, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (34, 1), (37, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (25, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (34, 1), (37, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (27, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 2), (32, 1), (34, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (23, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (54, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (27, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (37, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (40, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (43, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (24, 1), (27, 1), (32, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (27, 1), (32, 2), (46, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (8, 1), (32, 2), (34, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (14, 1), (24, 1), (27, 1), (32, 1), (54, 2), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (14, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (8, 1), (23, 1), (24, 1), (32, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (8, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (14, 1), (23, 1), (24, 1), (32, 1), (54, 2), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (14, 1), (24, 1), (32, 1), (34, 1), (49, 1), (54, 2)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (27, 1), (32, 1), (38, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (27, 1), (32, 1), (41, 1), (54, 2), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (38, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 2)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (38, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (32, 1), (41, 1), (54, 2), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (38, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (41, 1), (49, 1), (54, 2)] }, { coefficient := 1, powers := [(38, 1), (57, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (25, 1), (27, 1), (32, 2), (46, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (8, 1), (25, 1), (32, 2), (34, 1), (46, 1), (49, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (25, 1), (32, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (27, 1), (32, 1), (43, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (32, 1), (34, 1), (37, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (25, 1), (32, 1), (53, 2), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (25, 1), (27, 1), (32, 1), (43, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (25, 1), (32, 1), (34, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (25, 1), (32, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (25, 1), (27, 1), (32, 1), (43, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (25, 1), (32, 1), (34, 1), (37, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (29, 1), (41, 1), (49, 2), (60, 1)] }]
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
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB6_3
