import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB0_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "997058e1f887a6e457bdb493312741ac6bd64dc7222856633ac7237dabaf3ce6"
def certificateSHA256 : String := "515b9bfb392fd42eb6a2bb3fe9b81dbf1ead82a66494bf23a85d53f91a91a2ae"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 57 → Fin 608 := ![
  5,
  7,
  10,
  14,
  17,
  18,
  19,
  27,
  32,
  189,
  190,
  199,
  202,
  206,
  214,
  215,
  230,
  281,
  298,
  306,
  307,
  311,
  325,
  333,
  351,
  373,
  410,
  423,
  425,
  434,
  436,
  438,
  439,
  441,
  443,
  447,
  454,
  462,
  464,
  469,
  486,
  505,
  541,
  549,
  550,
  567,
  568,
  571,
  572,
  589,
  593,
  599,
  601,
  602,
  604,
  605,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 57 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 57 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (23, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (23, 1), (25, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (25, 1), (36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (19, 1), (29, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (29, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (23, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (23, 1), (30, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (30, 1), (36, 1), (42, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (24, 1), (29, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (29, 1), (44, 1), (47, 1), (56, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (29, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (29, 1), (44, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (30, 1), (36, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (30, 1), (36, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (40, 1), (42, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (42, 1), (44, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (40, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (42, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (40, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (44, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (23, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (30, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (42, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (38, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (30, 1), (36, 1), (42, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (23, 1), (25, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (25, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (23, 1), (25, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (23, 1), (25, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (25, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (24, 1), (42, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (25, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (20, 1), (24, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (29, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (35, 1), (36, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (42, 1), (47, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (30, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (19, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (47, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (36, 1), (47, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (42, 1), (48, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (23, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (24, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (36, 1), (42, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(19, 2), (23, 1), (42, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (23, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (36, 1), (42, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (25, 1), (36, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (32, 1), (36, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (36, 1), (42, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (32, 1), (36, 1), (42, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (35, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (30, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (19, 1), (23, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (24, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (19, 1), (35, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (19, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (19, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (35, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (35, 1), (36, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (35, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (19, 1), (23, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (19, 1), (23, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (23, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (23, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (36, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (30, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (27, 1), (42, 1), (48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (42, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (25, 1), (32, 1), (36, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (32, 1), (36, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (40, 1), (42, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (14, 1), (32, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (32, 1), (36, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (25, 1), (32, 1), (36, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (32, 1), (36, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (6, 1), (24, 1), (29, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (30, 1), (53, 1)] }, { coefficient := 2, powers := [(6, 2), (19, 1), (29, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (29, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (29, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (36, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (17, 1), (25, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (23, 1), (25, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (25, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (42, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (17, 1), (23, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (23, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (23, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (42, 1), (47, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (47, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (42, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (38, 1), (42, 1), (48, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (32, 1), (36, 1), (42, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (23, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (23, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (42, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (17, 1), (23, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (32, 1), (36, 1), (42, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (40, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (32, 1), (36, 1), (42, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (14, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (38, 1), (42, 1), (48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (42, 1), (48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (42, 1), (48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (13, 1), (24, 1), (29, 1), (47, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (19, 1), (29, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (29, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (42, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (30, 1), (36, 1), (42, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (17, 1), (23, 1), (25, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (23, 1), (25, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (42, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (17, 1), (23, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (36, 1), (42, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (32, 1), (36, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 2), (23, 1), (42, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (35, 1), (42, 1), (44, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (35, 1), (44, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (35, 1), (44, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (24, 1), (29, 1), (44, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (19, 1), (23, 1), (42, 1), (44, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (23, 1), (24, 1), (42, 1), (44, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (23, 1), (30, 1), (44, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (19, 1), (35, 1), (42, 1), (44, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (19, 1), (35, 1), (44, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (19, 1), (35, 1), (44, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (33, 1), (35, 1), (36, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 1), (35, 1), (36, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (35, 1), (44, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (27, 1), (42, 1), (45, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (36, 1), (42, 1), (44, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (35, 1), (36, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (19, 1), (29, 1), (44, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (23, 1), (42, 1), (44, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (17, 1), (23, 1), (25, 1), (36, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (17, 1), (23, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (23, 1), (25, 1), (36, 1), (42, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (23, 1), (36, 1), (42, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (23, 1), (44, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (23, 1), (33, 1), (36, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (23, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (36, 1), (42, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (29, 1), (30, 1), (36, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 2), (23, 1), (37, 1), (42, 1), (48, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 2), (23, 1), (40, 1), (42, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 2), (23, 1), (42, 1), (44, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (40, 1), (42, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (42, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (29, 1), (42, 1), (44, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (42, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (30, 1), (36, 1), (42, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (23, 1), (25, 1), (36, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (23, 1), (36, 1), (48, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (25, 1), (32, 1), (36, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (23, 1), (30, 1), (36, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (32, 1), (36, 1), (42, 1), (46, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (25, 1), (36, 1), (42, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (36, 1), (42, 1), (48, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (32, 1), (36, 1), (42, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (44, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (36, 1), (42, 1), (44, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (30, 1), (36, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (33, 1), (36, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(36, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(36, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (38, 1), (42, 1), (48, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (38, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (38, 1), (42, 1), (48, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (38, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (42, 1), (47, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (38, 1), (42, 1), (48, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (38, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -2, powers := [(14, 1), (17, 1), (23, 1), (25, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (25, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (25, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (32, 1), (36, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (42, 1), (48, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (19, 1), (42, 1), (48, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (19, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (36, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (6, 1), (18, 1), (24, 1), (29, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (29, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (29, 1), (30, 1), (53, 1)] }, { coefficient := -2, powers := [(6, 2), (18, 1), (19, 1), (29, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (19, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (18, 1), (29, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (19, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (19, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (27, 1), (42, 1), (43, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (19, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (36, 1), (42, 1), (48, 1), (57, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 57,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB0_2.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB0_2
