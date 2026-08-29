import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component50.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ccc6db4cc53e1596c65383efac5a2204db72493ca8e13866ac0a90bc9f5371e0"
def certificateSHA256 : String := "4eb86a801624cd0f5c4a71d5cded1cef1c589110dde8f052f93b363feb4881da"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 75 → Fin 638 := ![
  0,
  1,
  2,
  3,
  14,
  24,
  25,
  26,
  30,
  34,
  36,
  38,
  39,
  161,
  162,
  163,
  164,
  165,
  166,
  167,
  168,
  169,
  170,
  171,
  175,
  177,
  189,
  194,
  196,
  200,
  202,
  204,
  207,
  209,
  211,
  216,
  243,
  244,
  322,
  348,
  349,
  350,
  355,
  359,
  361,
  362,
  363,
  365,
  366,
  373,
  385,
  396,
  399,
  406,
  432,
  443,
  462,
  465,
  472,
  477,
  479,
  481,
  556,
  557,
  569,
  576,
  577,
  583,
  620,
  626,
  628,
  632,
  634,
  635,
  637
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 75 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }, { coefficient := 1, powers := [(29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 75 → SparsePoly (Fin 63) := ![
  [{ coefficient := 4, powers := [(0, 1), (9, 1), (25, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (9, 1), (62, 1)] }, { coefficient := 4, powers := [(0, 1), (25, 1), (40, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (31, 1), (37, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (40, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (36, 1), (40, 1), (42, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (34, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (15, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (36, 1), (42, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (36, 1), (42, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (20, 1), (44, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (15, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (43, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (34, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (20, 1), (33, 1), (47, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (20, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (20, 1), (33, 1), (47, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (33, 1), (43, 1), (47, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (36, 1), (37, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (25, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (39, 1), (58, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (20, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (39, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (24, 1), (31, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (25, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (44, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (44, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (50, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (55, 2), (56, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (25, 1), (30, 1), (39, 1), (47, 1), (50, 2), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (25, 1), (30, 1), (39, 1), (47, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (29, 1), (46, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (44, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (44, 1), (55, 1), (56, 1)] }, { coefficient := -4, powers := [(24, 1), (25, 1), (44, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (55, 2), (56, 1)] }, { coefficient := -4, powers := [(24, 1), (25, 1), (55, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (44, 1), (56, 1)] }, { coefficient := 2, powers := [(24, 1), (55, 1), (56, 1)] }, { coefficient := -6, powers := [(30, 1), (47, 1), (50, 1)] }, { coefficient := -4, powers := [(30, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (29, 1), (31, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (29, 1), (40, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (50, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (53, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(24, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(24, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (5, 1), (24, 1), (25, 1), (50, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 4, powers := [(2, 1), (5, 1), (24, 1), (25, 1), (53, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 4, powers := [(2, 1), (14, 1), (24, 1), (25, 1), (39, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (14, 1), (24, 1), (25, 1), (39, 1), (55, 2), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (42, 1), (50, 1)] }, { coefficient := 2, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (50, 1)] }, { coefficient := 2, powers := [(14, 1), (24, 1), (25, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(14, 1), (24, 1), (25, 1), (55, 2)] }, { coefficient := 2, powers := [(14, 1), (24, 1), (55, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (8, 1), (25, 1), (30, 1), (47, 1), (50, 2), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (8, 1), (25, 1), (30, 1), (47, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (19, 1), (25, 1), (30, 1), (39, 1), (50, 2), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (19, 1), (25, 1), (30, 1), (39, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (26, 1), (45, 1), (50, 1)] }, { coefficient := 2, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (44, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 2, powers := [(2, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (8, 1), (36, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (15, 1), (36, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (36, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1), (50, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1), (55, 1)] }, { coefficient := -4, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (15, 1), (18, 1), (25, 1), (33, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (18, 1), (33, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (25, 1), (53, 1)] }],
  [{ coefficient := -4, powers := [(5, 1), (18, 1), (20, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (18, 1), (24, 1), (25, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (18, 1), (24, 1), (25, 1), (39, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (50, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (18, 1), (25, 1), (30, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (18, 1), (25, 1), (30, 1), (39, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (18, 1), (24, 1), (25, 1), (39, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (18, 1), (24, 1), (25, 1), (39, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (42, 1), (50, 1)] }, { coefficient := -2, powers := [(2, 1), (42, 1), (52, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (25, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (25, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (8, 1), (25, 1), (30, 1), (42, 1), (50, 2), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (8, 1), (25, 1), (30, 1), (42, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (14, 1), (25, 1), (30, 1), (39, 1), (50, 2), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (14, 1), (25, 1), (30, 1), (39, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (18, 1), (25, 1), (30, 1), (39, 1), (50, 1), (51, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (18, 1), (25, 1), (30, 1), (39, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(14, 1), (30, 1), (50, 1)] }, { coefficient := 2, powers := [(18, 1), (30, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (46, 1), (56, 1)] }, { coefficient := 4, powers := [(18, 1), (24, 1), (25, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (5, 1), (24, 1), (25, 1), (50, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := -4, powers := [(2, 1), (5, 1), (24, 1), (25, 1), (55, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := -4, powers := [(2, 1), (19, 1), (24, 1), (25, 1), (39, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := -4, powers := [(2, 1), (19, 1), (24, 1), (25, 1), (39, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(2, 1), (47, 1), (55, 1)] }, { coefficient := -4, powers := [(5, 1), (36, 1), (44, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (25, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (25, 1), (58, 1), (62, 1)] }, { coefficient := 4, powers := [(5, 1), (20, 1), (36, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(14, 1), (24, 1), (25, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(25, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(25, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(20, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(25, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (31, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (34, 1), (37, 1), (40, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (15, 1), (25, 1), (33, 1), (40, 1), (47, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (33, 1), (47, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (20, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (15, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (40, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (34, 1), (37, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (25, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (33, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(25, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (25, 1), (46, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (25, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(25, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (31, 1), (42, 1), (54, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (31, 1), (47, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (47, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (31, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (20, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (45, 1), (50, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (45, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (25, 1), (40, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (45, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (45, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (50, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (51, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (33, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (45, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (50, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (51, 1), (55, 1), (56, 1)] }, { coefficient := -4, powers := [(24, 1), (25, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 4, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(24, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (18, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (18, 1), (26, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (18, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (26, 1), (42, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (26, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (15, 1), (25, 1), (33, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (33, 1), (60, 1)] }, { coefficient := -4, powers := [(2, 1), (8, 1), (25, 1), (30, 1), (42, 1), (50, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (8, 1), (25, 1), (30, 1), (42, 1), (55, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (14, 1), (25, 1), (30, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (14, 1), (25, 1), (30, 1), (39, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (34, 1), (40, 1), (50, 1), (62, 1)] }, { coefficient := -4, powers := [(2, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (34, 1), (37, 1), (40, 1), (62, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (25, 1), (30, 1), (39, 1), (50, 1), (51, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (25, 1), (30, 1), (39, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(25, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(25, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(53, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(25, 1), (47, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (20, 1), (50, 1)] }, { coefficient := 2, powers := [(8, 1), (20, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (24, 1), (25, 2), (39, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (24, 1), (25, 2), (39, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 2), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 2), (55, 1), (56, 1)] }, { coefficient := 4, powers := [(24, 1), (25, 2), (56, 1), (60, 1)] }, { coefficient := -4, powers := [(24, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (29, 1), (42, 1), (62, 1)] }, { coefficient := 4, powers := [(2, 1), (25, 2), (30, 1), (39, 1), (42, 1), (50, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (25, 2), (30, 1), (39, 1), (42, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(25, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (20, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (25, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (25, 1), (47, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (25, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (25, 1), (39, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (25, 1), (42, 1), (50, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (25, 1), (42, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (14, 1), (25, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (14, 1), (25, 1), (39, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (14, 1), (58, 1)] }, { coefficient := 2, powers := [(14, 1), (25, 1), (50, 1)] }, { coefficient := 2, powers := [(14, 1), (25, 1), (55, 1)] }, { coefficient := 2, powers := [(14, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (39, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 2), (25, 1), (39, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 2), (25, 1), (39, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (25, 1), (30, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (25, 1), (30, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (24, 1), (25, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (24, 1), (25, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 6, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (15, 1), (33, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (33, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (34, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(30, 1), (50, 1)] }, { coefficient := 2, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (15, 1), (31, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (31, 1), (54, 1)] }, { coefficient := -2, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (25, 1), (30, 1), (39, 1), (42, 1), (50, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (25, 1), (30, 1), (39, 1), (42, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (25, 1), (30, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (25, 1), (30, 1), (39, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(30, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (24, 1), (25, 1), (39, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (50, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (55, 1)] }, { coefficient := 2, powers := [(24, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (25, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (42, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (9, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (49, 1)] }, { coefficient := 2, powers := [(0, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (15, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(25, 1), (44, 1)] }, { coefficient := -2, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (9, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (15, 1), (44, 1)] }, { coefficient := -2, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (33, 1), (47, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (36, 1), (42, 1)] }, { coefficient := 2, powers := [(8, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1), (42, 1), (43, 1)] }, { coefficient := -2, powers := [(8, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (25, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(25, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (25, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (25, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (39, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (58, 1)] }, { coefficient := -2, powers := [(25, 1), (50, 1)] }, { coefficient := -2, powers := [(25, 1), (55, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (26, 1), (42, 1), (45, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (41, 1), (42, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (45, 1), (52, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (15, 1), (25, 1), (33, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (33, 1), (47, 1), (50, 1)] }, { coefficient := -2, powers := [(2, 2), (25, 1), (39, 2), (50, 1), (59, 2)] }, { coefficient := -2, powers := [(2, 2), (25, 1), (39, 2), (55, 1), (59, 2)] }, { coefficient := -2, powers := [(2, 2), (25, 1), (39, 1), (42, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 2), (25, 1), (39, 1), (42, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 2), (25, 1), (39, 1), (47, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 2), (25, 1), (39, 1), (47, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (39, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (42, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 4, powers := [(2, 1), (5, 1), (24, 1), (25, 1), (50, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (5, 1), (24, 1), (25, 1), (53, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (30, 1), (39, 1), (50, 1), (59, 2)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (30, 1), (39, 1), (55, 1), (59, 2)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (30, 1), (42, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (30, 1), (42, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (30, 1), (47, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (30, 1), (47, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (24, 1), (25, 1), (39, 1), (50, 1), (59, 2)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (24, 1), (25, 1), (39, 1), (55, 1), (59, 2)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (24, 1), (25, 1), (42, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (24, 1), (25, 1), (42, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (24, 1), (25, 1), (47, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (24, 1), (25, 1), (47, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (19, 1), (24, 1), (25, 1), (39, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (19, 1), (24, 1), (25, 1), (39, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (37, 1), (39, 1), (58, 1), (59, 1)] }, { coefficient := -6, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := -4, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := -6, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (25, 1), (33, 1), (40, 1), (47, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := -4, powers := [(18, 1), (24, 1), (25, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (26, 1), (42, 1), (45, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (42, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (42, 1), (45, 1), (52, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (42, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (31, 1), (50, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (34, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (15, 1), (25, 1), (33, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (15, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (33, 1), (47, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (36, 1), (37, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (36, 1), (40, 1), (42, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (36, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (9, 1), (20, 1), (50, 1), (54, 1)] }, { coefficient := -4, powers := [(0, 1), (9, 1), (25, 1), (43, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (43, 1)] }, { coefficient := -2, powers := [(0, 1), (15, 1), (20, 1), (44, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (15, 1), (25, 1), (40, 1), (44, 1)] }, { coefficient := -2, powers := [(0, 1), (15, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (31, 1), (37, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (37, 1), (50, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := -4, powers := [(0, 1), (20, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (43, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (38, 1), (58, 1)] }, { coefficient := -4, powers := [(0, 1), (25, 1), (40, 1), (43, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (41, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (43, 1), (49, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (50, 2)] }, { coefficient := -2, powers := [(0, 1), (31, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (34, 1), (37, 1), (40, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (40, 1), (43, 1)] }, { coefficient := -2, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (44, 1)] }, { coefficient := -2, powers := [(0, 1), (50, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 4, powers := [(2, 1), (37, 1), (39, 1), (58, 1), (59, 1)] }, { coefficient := 4, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (34, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(3, 1), (25, 1), (44, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (25, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (50, 1), (56, 1)] }, { coefficient := -4, powers := [(5, 1), (20, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (33, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (20, 1), (33, 1), (47, 1), (48, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (20, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(8, 1), (20, 1), (33, 1), (47, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (43, 1), (48, 1)] }, { coefficient := -2, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (33, 1), (37, 1), (47, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (33, 1), (40, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (36, 1), (40, 1), (42, 1), (43, 1)] }, { coefficient := 2, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (42, 1), (43, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (36, 1), (37, 1), (42, 1), (48, 1)] }, { coefficient := -2, powers := [(14, 1), (24, 1), (25, 1), (44, 1), (56, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (44, 1), (50, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (44, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (50, 2)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(25, 1), (44, 1)] }, { coefficient := -2, powers := [(25, 1), (50, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (4 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 75,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((4 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (4 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (4 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component50.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component50.SelectedLeafB7
