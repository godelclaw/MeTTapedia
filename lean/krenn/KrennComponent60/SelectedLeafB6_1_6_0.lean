import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_1_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5f8b42cf7fbc5ede204f6a0f2f4c91892459b8a88c644e8fea35d95fadde58a4"
def certificateSHA256 : String := "f29e5190fcc79dbf5b3365a0eeda50b3cb3a4da1d903e1c8c8f794e34b22f173"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 47 → Fin 668 := ![
  13,
  22,
  147,
  149,
  168,
  239,
  293,
  298,
  301,
  302,
  314,
  316,
  403,
  404,
  423,
  432,
  436,
  443,
  444,
  455,
  457,
  459,
  466,
  517,
  548,
  556,
  558,
  578,
  582,
  587,
  600,
  601,
  609,
  632,
  645,
  650,
  653,
  655,
  657,
  658,
  659,
  660,
  661,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (22, 2), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (22, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (12, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (36, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (26, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (32, 1), (36, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (22, 1), (62, 2)] }, { coefficient := -2, powers := [(0, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (55, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (32, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (35, 1), (36, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (24, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (26, 1), (33, 1), (36, 1), (52, 1)] }, { coefficient := -2, powers := [(9, 1), (24, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (52, 1), (55, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (35, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (19, 1), (33, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (35, 1), (36, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (21, 1), (35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (55, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (45, 1), (55, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (33, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (35, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (26, 1), (35, 1), (36, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (12, 1), (33, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (35, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (52, 1), (55, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (55, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (21, 1), (35, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (33, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (22, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (33, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (33, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (33, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (41, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (15, 1), (22, 1), (27, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (27, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (26, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (35, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (21, 1), (35, 1), (36, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (12, 1), (21, 1), (33, 1), (35, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (21, 1), (26, 1), (35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (55, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (33, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (9, 1), (32, 1), (33, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (30, 1), (32, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (32, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (24, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (18, 1), (24, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (19, 1), (24, 1), (33, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (46, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (32, 1), (36, 1), (48, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (21, 1), (35, 1), (36, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (21, 1), (35, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (26, 1), (35, 1), (36, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (26, 1), (33, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (24, 1), (33, 1), (36, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (26, 1), (35, 1), (36, 1), (40, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (26, 1), (35, 1), (36, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (26, 1), (35, 1), (36, 1), (41, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (26, 1), (33, 1), (36, 1), (40, 1), (52, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (24, 1), (33, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (40, 1), (52, 1), (55, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (45, 1), (52, 1), (55, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (45, 1), (55, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (47, 1), (52, 1), (55, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (30, 1), (36, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (30, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (30, 1), (36, 1), (42, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (30, 1), (36, 1), (40, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(39, 1), (42, 1)] }, { coefficient := -1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (9, 1), (33, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (12, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (19, 1), (33, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (47, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (33, 1), (36, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (30, 1), (36, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1), (42, 1), (47, 1), (50, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_1_6_0.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_1_6_0
