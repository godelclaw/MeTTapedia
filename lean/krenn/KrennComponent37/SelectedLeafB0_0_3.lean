import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_0_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7d94973cd8901a221c4c66a452748c567fe9cac9bda0f2b238349dac6c1383b4"
def certificateSHA256 : String := "9f1b28efb763407bef567b821981ad76755b259611d3e9721b488904de371f9e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 47 → Fin 667 := ![
  170,
  171,
  175,
  180,
  181,
  183,
  256,
  257,
  260,
  280,
  285,
  307,
  310,
  311,
  316,
  317,
  342,
  393,
  410,
  411,
  424,
  432,
  433,
  436,
  438,
  446,
  450,
  454,
  458,
  472,
  475,
  479,
  483,
  487,
  566,
  570,
  596,
  608,
  645,
  650,
  657,
  658,
  660,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (52, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (47, 1), (53, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1), (54, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (47, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (46, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (46, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (54, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (24, 1), (26, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (51, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (30, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(49, 1), (54, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (49, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(48, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (49, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (21, 1), (30, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (29, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (24, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (24, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (21, 1), (30, 1), (47, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (47, 1), (54, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1), (49, 1), (54, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (49, 1), (54, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (49, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (38, 1), (58, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (47, 1), (52, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (47, 1), (55, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (29, 1), (38, 1), (55, 1), (58, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (29, 1), (46, 1), (52, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (46, 1), (51, 1), (54, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (46, 1), (55, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (48, 1), (52, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(37, 1), (48, 1), (53, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (49, 1), (55, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (58, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1), (51, 1), (54, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(48, 1), (51, 1), (52, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (20, 1), (24, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (58, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (21, 1), (29, 1), (55, 1), (57, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (44, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (28, 1), (49, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (26, 1), (44, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (44, 1), (55, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (29, 1), (49, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (26, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (29, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 2), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (49, 1), (54, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (55, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_0_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_0_3
