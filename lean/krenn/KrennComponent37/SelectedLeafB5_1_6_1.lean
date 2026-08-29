import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_1_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8a28348355b34eb2d301aa975c15c9809b12a1bf2fda9f37115323413ea10218"
def certificateSHA256 : String := "f26d3a34692197a7f3450936cb0639df188d497ec72afc9fcbcfd95c5eb6a0dd"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 670 := ![
  5,
  171,
  280,
  294,
  295,
  298,
  299,
  312,
  313,
  317,
  394,
  410,
  411,
  424,
  430,
  446,
  447,
  450,
  466,
  474,
  482,
  505,
  510,
  519,
  561,
  580,
  604,
  638,
  646,
  656,
  657,
  658,
  659,
  660,
  662,
  664,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(4, 1), (6, 1), (36, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (26, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (26, 1), (42, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (42, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (42, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (26, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (36, 1), (52, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (36, 1), (46, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (15, 1), (22, 1), (36, 1), (55, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (26, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (33, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (36, 1), (39, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (36, 1), (39, 1), (51, 1), (56, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (30, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (42, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (26, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (22, 1), (36, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (22, 1), (36, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (22, 1), (36, 1), (55, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (6, 1), (36, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (39, 1), (51, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (22, 1), (30, 1), (36, 1), (55, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (36, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (39, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (36, 1), (38, 1), (55, 1), (60, 2)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (36, 1), (46, 1), (52, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (28, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (6, 1), (36, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (7, 1), (35, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (15, 1), (22, 1), (30, 1), (36, 1), (55, 1), (60, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (36, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (21, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (41, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (46, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (26, 1), (42, 1), (44, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (26, 1), (49, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (42, 1), (44, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (49, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (49, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (6, 1), (22, 1), (36, 1), (46, 1), (55, 1), (60, 2)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (6, 1), (22, 1), (36, 1), (52, 1), (55, 1), (60, 2)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (6, 1), (32, 1), (36, 1), (38, 1), (55, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (22, 1), (36, 1), (46, 2), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (22, 1), (36, 1), (46, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (32, 1), (36, 1), (38, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (15, 1), (22, 1), (36, 1), (41, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (15, 1), (22, 1), (36, 1), (41, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (15, 1), (32, 1), (36, 1), (38, 1), (41, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (33, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (36, 1), (39, 1), (45, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (36, 1), (39, 1), (41, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (26, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (30, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (39, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (36, 1), (39, 1), (41, 1), (51, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (36, 1), (39, 1), (45, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (36, 1), (39, 1), (46, 1), (51, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (26, 1), (41, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (49, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (41, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (44, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (42, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1)] }, { coefficient := -1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (6, 1), (18, 1), (36, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (15, 1), (36, 1), (41, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (7, 1), (22, 1), (36, 1), (55, 1), (60, 2)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (22, 1), (36, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (15, 1), (22, 1), (36, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (15, 1), (22, 1), (36, 1), (52, 1), (55, 1), (60, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_1_6_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_1_6_1
