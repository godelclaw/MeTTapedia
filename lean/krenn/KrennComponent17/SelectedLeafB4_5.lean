import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d3bb1f616a08f8bc89ddd990f303123970901dbf791e571030ebc4aa548c4c7e"
def certificateSHA256 : String := "6fbf31b995b9ab67ecccf943e9f9e77a903d06f36f70b6d45adce2f67548760e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 59 → Fin 608 := ![
  5,
  7,
  8,
  10,
  12,
  14,
  16,
  19,
  20,
  22,
  27,
  30,
  31,
  32,
  33,
  34,
  40,
  41,
  42,
  188,
  189,
  190,
  202,
  213,
  300,
  307,
  308,
  309,
  312,
  318,
  325,
  327,
  334,
  364,
  373,
  400,
  423,
  434,
  495,
  505,
  518,
  549,
  550,
  553,
  556,
  567,
  569,
  570,
  571,
  572,
  587,
  599,
  600,
  601,
  602,
  603,
  604,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 59 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 59 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (38, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (36, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (23, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (23, 1), (25, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (25, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (38, 1), (41, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (23, 1), (24, 1), (38, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (41, 1), (61, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (38, 1), (48, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(24, 1), (35, 1), (38, 1), (41, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (19, 1), (23, 1), (38, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (35, 1), (38, 1), (41, 1), (61, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (38, 1), (48, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(19, 1), (35, 1), (38, 1), (41, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (8, 1), (23, 1), (39, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (35, 1), (39, 1), (41, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (23, 1), (30, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (41, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (30, 1), (36, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (21, 1), (35, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (21, 1), (35, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (35, 1), (37, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (20, 1), (23, 1), (36, 1), (52, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (35, 1), (36, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(20, 1), (23, 1), (36, 1), (48, 1), (52, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(20, 1), (35, 1), (36, 1), (41, 1), (48, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (35, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (29, 1), (50, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (57, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (23, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (50, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (23, 1), (42, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (35, 1), (41, 1), (42, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (14, 1), (23, 1), (39, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (14, 1), (35, 1), (39, 1), (41, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (42, 1), (48, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (35, 1), (41, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (25, 1), (45, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (36, 1), (38, 1), (47, 1), (50, 1), (57, 1), (61, 2)] }],
  [{ coefficient := 4, powers := [(4, 1), (5, 1), (35, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (35, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (29, 1), (50, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (29, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (35, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (35, 1), (44, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (35, 1), (50, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (16, 1), (31, 1), (50, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (15, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (25, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (38, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (31, 1), (50, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (31, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (23, 1), (36, 1), (52, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(9, 1), (35, 1), (36, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(23, 1), (36, 1), (48, 1), (52, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(35, 1), (36, 1), (41, 1), (48, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (38, 1), (47, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (38, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (29, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (32, 1), (36, 1), (38, 1), (50, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (50, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (19, 1), (23, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (19, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (28, 1), (31, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (32, 1), (36, 1), (38, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (23, 1), (36, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(9, 1), (35, 1), (36, 1), (41, 1), (61, 1)] }, { coefficient := -2, powers := [(23, 1), (36, 1), (48, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(35, 1), (36, 1), (41, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (23, 1), (38, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(9, 1), (35, 1), (38, 1), (41, 1), (61, 1)] }, { coefficient := 2, powers := [(23, 1), (38, 1), (48, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(35, 1), (38, 1), (41, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (25, 1), (32, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (25, 1), (59, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (50, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (38, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (23, 1), (39, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (35, 1), (39, 1), (41, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (23, 1), (30, 1), (58, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := -2, powers := [(8, 1), (19, 1), (23, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (23, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (41, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (26, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (41, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (25, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (50, 2), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (50, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (44, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (58, 1)] }, { coefficient := 2, powers := [(41, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (8, 1), (23, 1), (39, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 2), (8, 1), (35, 1), (39, 1), (41, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (8, 1), (23, 1), (30, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (8, 1), (30, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (32, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (8, 1), (23, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (8, 1), (33, 1), (35, 1), (39, 1), (41, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (14, 1), (23, 1), (24, 1), (39, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (14, 1), (24, 1), (35, 1), (39, 1), (41, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (19, 1), (23, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (19, 1), (35, 1), (41, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (23, 1), (55, 1)] }, { coefficient := 2, powers := [(1, 1), (5, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(1, 1), (5, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (6, 1), (8, 1), (23, 1), (30, 1), (33, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (6, 1), (8, 1), (30, 1), (33, 1), (35, 1), (41, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (14, 1), (23, 1), (24, 1), (30, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (14, 1), (24, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (26, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (26, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (43, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (32, 1), (43, 1)] }, { coefficient := 2, powers := [(6, 1), (8, 1), (19, 1), (23, 1), (33, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (8, 1), (19, 1), (33, 1), (35, 1), (41, 1), (48, 1)] }, { coefficient := 2, powers := [(8, 1), (14, 1), (19, 1), (23, 1), (24, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (14, 1), (19, 1), (24, 1), (35, 1), (41, 1), (48, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (43, 1), (59, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (24, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (35, 1), (38, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (14, 1), (23, 1), (39, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (14, 1), (35, 1), (39, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (14, 1), (23, 1), (30, 1), (58, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (14, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (23, 1), (24, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := -4, powers := [(4, 1), (5, 1), (26, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (26, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (26, 1), (29, 1), (50, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (26, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (26, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (26, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (26, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (34, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (32, 1), (43, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (23, 1), (24, 1), (42, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (24, 1), (35, 1), (41, 1), (42, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (33, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (23, 1), (24, 1), (39, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (23, 1), (30, 1), (36, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (24, 1), (35, 1), (39, 1), (41, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (30, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (24, 1), (42, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (33, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(8, 1), (33, 1), (35, 1), (36, 1), (41, 1), (48, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (45, 1), (59, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (25, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (32, 1), (36, 1), (38, 1), (47, 1), (50, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (35, 1), (38, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 59,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_5
