import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_6_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d41d809175e1322ca340e151103a836d546373af4b72aedb9968bc4c8bbb6b8e"
def certificateSHA256 : String := "0402446b7d5c2bbb65f013fed58a1cc10683845b1ff7733d46466887ffa9050b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 673 := ![
  6,
  18,
  23,
  24,
  148,
  167,
  168,
  171,
  175,
  179,
  181,
  184,
  185,
  216,
  279,
  280,
  294,
  296,
  297,
  298,
  299,
  315,
  316,
  319,
  334,
  370,
  438,
  450,
  454,
  476,
  480,
  482,
  483,
  485,
  566,
  605,
  625,
  626,
  656,
  657,
  658,
  659,
  661,
  663,
  666,
  667,
  668,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (22, 1), (33, 1), (36, 1), (39, 1), (52, 1), (55, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (33, 1), (36, 1), (39, 1), (52, 1), (55, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(36, 1), (51, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(36, 1), (55, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (33, 2), (39, 2), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (33, 2), (39, 2), (52, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (12, 1), (19, 1), (24, 1), (33, 1), (39, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (19, 1), (24, 1), (33, 1), (39, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (19, 1), (33, 1), (39, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (19, 1), (33, 1), (39, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 2), (33, 2), (39, 1), (49, 1), (52, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 2), (33, 2), (39, 1), (49, 1), (52, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (22, 1), (24, 1), (33, 1), (39, 1), (45, 1), (52, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (24, 1), (33, 1), (39, 1), (45, 1), (52, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (61, 1), (69, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (44, 1), (46, 1)] }, { coefficient := -2, powers := [(24, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (67, 1)] }, { coefficient := 2, powers := [(24, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (20, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (19, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (33, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (19, 1), (22, 1), (24, 1), (33, 1), (39, 1), (52, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (22, 1), (24, 1), (33, 1), (39, 1), (52, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(24, 1), (61, 1), (69, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (46, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (47, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (41, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (60, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (22, 1), (33, 1), (39, 1), (52, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (33, 1), (39, 1), (52, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(61, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (24, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (33, 2), (39, 1), (49, 1), (52, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (24, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (33, 2), (39, 1), (49, 1), (52, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (12, 1), (19, 1), (22, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (19, 1), (22, 1), (33, 1), (39, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (19, 1), (22, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (22, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (33, 1), (38, 1), (39, 1), (59, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (38, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (46, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (18, 1), (19, 1), (22, 1), (24, 1), (26, 1), (33, 1), (39, 1), (45, 1), (52, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (19, 1), (22, 1), (24, 1), (26, 1), (33, 1), (39, 1), (45, 1), (52, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (45, 1), (61, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (19, 1), (22, 1), (33, 1), (39, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (19, 1), (22, 1), (33, 1), (39, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (19, 1), (22, 1), (33, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (19, 1), (22, 1), (33, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 2), (22, 1), (30, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 2), (22, 1), (30, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (29, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (19, 1), (22, 1), (33, 2), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (19, 1), (22, 1), (33, 2), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (19, 1), (22, 1), (24, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (19, 1), (22, 1), (33, 2), (39, 1), (49, 1), (52, 1), (71, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (19, 1), (22, 1), (24, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (19, 1), (22, 1), (33, 2), (39, 1), (49, 1), (52, 1), (71, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (33, 1), (39, 1), (59, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (33, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (33, 1), (39, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (19, 1), (22, 1), (33, 1), (39, 2), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (19, 1), (22, 1), (33, 1), (39, 2), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (19, 1), (22, 1), (30, 1), (33, 1), (39, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (19, 1), (22, 1), (33, 1), (36, 1), (39, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (19, 1), (22, 1), (30, 1), (33, 1), (39, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (19, 1), (22, 1), (33, 1), (36, 1), (39, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (33, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (19, 1), (22, 1), (33, 2), (39, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (19, 1), (22, 1), (33, 2), (39, 1), (49, 1), (52, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 49,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_6_5_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_6_5_7
