import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "78d462a81958746106e24b31ea74dfff2eb9d7a66d9c3c5a1e5ec1dede878eb6"
def certificateSHA256 : String := "ee26581784aed2292c21f48f9821502e9ed39510884f1ba7e48dbe6de8a95886"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 664 := ![
  8,
  16,
  19,
  151,
  152,
  170,
  171,
  178,
  179,
  180,
  181,
  225,
  294,
  295,
  297,
  302,
  313,
  317,
  424,
  429,
  430,
  432,
  433,
  438,
  440,
  445,
  446,
  449,
  450,
  453,
  458,
  465,
  475,
  476,
  487,
  530,
  570,
  581,
  608,
  617,
  619,
  628,
  645,
  657,
  658,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (25, 1), (52, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (37, 1), (52, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (44, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (49, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (37, 1), (46, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (37, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (37, 2), (46, 1), (54, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (37, 2), (46, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (39, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (37, 2), (46, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(24, 1), (37, 2), (54, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (44, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (37, 1), (39, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (44, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 2), (48, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1), (39, 1), (51, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (30, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (26, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (39, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (39, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (39, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (49, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (21, 1), (52, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (37, 1), (52, 1), (55, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (50, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (50, 1), (51, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (37, 2), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (51, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (52, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (37, 1), (52, 1), (55, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (44, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (47, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (47, 1), (51, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (29, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (37, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(37, 2), (54, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (37, 2), (54, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 2), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (37, 2), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (28, 1), (37, 2), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 2), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (26, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(37, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (29, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(37, 2), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (49, 1), (52, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (49, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (37, 1), (49, 1), (52, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (38, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (39, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (49, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (26, 1), (47, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (29, 1), (47, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (29, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (38, 1), (60, 2)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (46, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (60, 2)] }, { coefficient := -1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (21, 1), (44, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (37, 1), (44, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (23, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (28, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (30, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (21, 1), (30, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (28, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (28, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (28, 1), (37, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (28, 1), (37, 2), (46, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (30, 1), (37, 2), (46, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (37, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (37, 2), (46, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (37, 2), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (37, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (39, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (37, 2), (48, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (37, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (23, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (29, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (39, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (26, 1), (36, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (26, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (28, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (28, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (28, 1), (37, 2), (54, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (37, 2), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 2), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 49,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_4
