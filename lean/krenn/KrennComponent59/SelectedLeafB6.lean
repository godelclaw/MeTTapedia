import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b3cb195cd79306e6707ae2bf1acc5a004fe2cc58aef12a66868af6537d7d78e2"
def certificateSHA256 : String := "95321f6143888320828ee46496090370985007ec50e11919bb02526b80db75bc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 614 := ![
  6,
  9,
  11,
  15,
  19,
  20,
  21,
  23,
  25,
  26,
  29,
  35,
  192,
  195,
  196,
  197,
  198,
  203,
  215,
  220,
  222,
  247,
  337,
  338,
  341,
  349,
  355,
  363,
  395,
  396,
  426,
  457,
  471,
  487,
  489,
  497,
  502,
  559,
  560,
  577,
  578,
  580,
  583,
  610,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 60) := ![
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (28, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (22, 1), (26, 1), (42, 1), (57, 2)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (22, 1), (26, 1), (49, 1), (57, 2)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (22, 1), (29, 1), (42, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (22, 1), (29, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := 4, powers := [(0, 1), (3, 1), (5, 1), (22, 1), (32, 1), (42, 1), (51, 1), (57, 1)] }, { coefficient := -4, powers := [(0, 1), (3, 1), (5, 1), (22, 1), (32, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (29, 1), (42, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (29, 1), (45, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (33, 1), (38, 1), (53, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (26, 1), (57, 2)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (29, 1), (54, 1), (57, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (22, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (26, 1), (29, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := -2, powers := [(3, 1), (29, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (25, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (8, 1), (24, 1), (26, 1), (29, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (8, 1), (24, 1), (26, 1), (29, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (24, 1), (26, 1), (29, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (20, 1), (23, 1), (32, 1), (37, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (23, 1), (32, 1), (44, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (23, 1), (32, 1), (44, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (5, 1), (20, 1), (32, 1), (37, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (8, 1), (20, 1), (22, 1), (32, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (8, 1), (20, 1), (22, 1), (32, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (20, 1), (32, 1), (37, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (20, 1), (32, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (20, 1), (22, 1), (32, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (32, 1), (59, 1)] }, { coefficient := 4, powers := [(17, 1), (20, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (42, 1), (44, 1), (57, 2)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (44, 1), (49, 1), (57, 2)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (29, 1), (42, 1), (44, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (29, 1), (44, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := 4, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (42, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := -4, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (44, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (26, 1), (44, 1), (57, 2)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (29, 1), (44, 1), (54, 1), (57, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (32, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (5, 1), (22, 1), (23, 1), (26, 1), (42, 1), (50, 1), (57, 1)] }, { coefficient := 4, powers := [(0, 1), (5, 1), (22, 1), (23, 1), (26, 1), (49, 1), (50, 1), (57, 1)] }, { coefficient := 4, powers := [(5, 1), (22, 1), (23, 1), (26, 1), (50, 1), (57, 1)] }, { coefficient := -2, powers := [(22, 1), (23, 1), (50, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (26, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := -4, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (26, 1), (49, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (37, 1), (49, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := -4, powers := [(5, 1), (12, 1), (22, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (49, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (10, 1), (29, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (8, 1), (32, 1), (42, 1), (44, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (8, 1), (32, 1), (44, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (17, 1), (26, 1), (42, 1), (44, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (17, 1), (26, 1), (44, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (37, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (32, 1), (44, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (17, 1), (26, 1), (44, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (32, 1), (37, 1), (49, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (32, 1), (37, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (49, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (8, 1), (26, 1), (29, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (8, 1), (26, 1), (29, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (26, 1), (29, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (23, 1), (32, 1), (37, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (32, 1), (44, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (32, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (5, 1), (32, 1), (37, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (8, 1), (22, 1), (32, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (8, 1), (22, 1), (32, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (32, 1), (37, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (32, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (22, 1), (32, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (59, 1)] }, { coefficient := -4, powers := [(17, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (5, 1), (22, 1), (26, 1), (42, 1), (50, 1), (54, 1), (57, 1)] }, { coefficient := -4, powers := [(0, 1), (5, 1), (22, 1), (26, 1), (49, 1), (50, 1), (54, 1), (57, 1)] }, { coefficient := -4, powers := [(5, 1), (22, 1), (26, 1), (50, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(22, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 2), (26, 1), (42, 1), (57, 2)] }, { coefficient := -2, powers := [(0, 1), (5, 2), (26, 1), (49, 1), (57, 2)] }, { coefficient := 2, powers := [(0, 1), (5, 2), (29, 1), (42, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 2), (29, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := 4, powers := [(0, 1), (5, 2), (32, 1), (42, 1), (51, 1), (57, 1)] }, { coefficient := -4, powers := [(0, 1), (5, 2), (32, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (12, 1), (26, 1), (42, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (12, 1), (26, 1), (45, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (37, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 2), (26, 1), (57, 2)] }, { coefficient := -2, powers := [(5, 2), (29, 1), (54, 1), (57, 1)] }, { coefficient := -4, powers := [(5, 2), (32, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (12, 1), (26, 1), (45, 1), (57, 1)] }, { coefficient := 4, powers := [(5, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (42, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(51, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (42, 1), (45, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (45, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (22, 1), (42, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (22, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (42, 1), (45, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (45, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (26, 1), (45, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (45, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(45, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (22, 1), (26, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (22, 1), (26, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (26, 1), (57, 1)] }, { coefficient := 2, powers := [(22, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (8, 1), (29, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (8, 1), (29, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (12, 1), (26, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (12, 1), (26, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (29, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (12, 1), (26, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (32, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (20, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (5, 1), (22, 1), (26, 1), (42, 1), (54, 1), (57, 1)] }, { coefficient := 4, powers := [(0, 1), (5, 1), (22, 1), (26, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := 4, powers := [(5, 1), (22, 1), (26, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (8, 1), (32, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (8, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (17, 1), (26, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (17, 1), (26, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (32, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (17, 1), (26, 1), (57, 1)] }, { coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (42, 1), (57, 2)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (49, 1), (57, 2)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (29, 1), (42, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (29, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := -4, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (42, 1), (51, 1), (57, 1)] }, { coefficient := 4, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (26, 1), (57, 2)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (29, 1), (54, 1), (57, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (37, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (32, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (29, 1), (37, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (32, 1), (37, 1), (51, 1)] }, { coefficient := 2, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (20, 1), (26, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 2), (5, 1), (32, 1), (37, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (8, 1), (22, 1), (32, 1), (42, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (8, 1), (22, 1), (32, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (8, 1), (26, 1), (29, 1), (42, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (8, 1), (26, 1), (29, 1), (45, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (29, 1), (37, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (32, 1), (37, 1), (51, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (32, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (22, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (26, 1), (29, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (32, 1), (37, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (32, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (32, 1), (44, 1), (50, 1)] }, { coefficient := 4, powers := [(17, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (35, 1), (42, 1), (56, 1), (57, 2)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (35, 1), (49, 1), (56, 1), (57, 2)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (42, 1), (45, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (45, 1), (49, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (29, 1), (35, 1), (42, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (5, 1), (29, 1), (35, 1), (49, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := 4, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (35, 1), (42, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := -4, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (35, 1), (49, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (22, 1), (42, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (22, 1), (49, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (35, 1), (42, 1), (57, 2)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (35, 1), (49, 1), (57, 2)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (38, 1), (42, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (38, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (42, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (45, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (26, 1), (35, 1), (56, 1), (57, 2)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (26, 1), (45, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (29, 1), (35, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (32, 1), (35, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (35, 1), (57, 2)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (38, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(35, 1), (57, 1)] }, { coefficient := 2, powers := [(38, 1), (54, 1)] }, { coefficient := -2, powers := [(45, 1), (51, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component59.SelectedLeafB6.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB6
