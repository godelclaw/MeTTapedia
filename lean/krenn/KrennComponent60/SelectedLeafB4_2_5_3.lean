import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cce738e6de7d7d96b6e077a9b18a76db770504a80e584d50f5d854320dc1e671"
def certificateSHA256 : String := "fae348822def2d140f955bb7cba472c71bcd1a954808335ad08fab4cced7455f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 668 := ![
  7,
  22,
  24,
  25,
  149,
  150,
  151,
  179,
  194,
  206,
  212,
  292,
  293,
  301,
  302,
  312,
  316,
  359,
  404,
  443,
  454,
  556,
  578,
  579,
  583,
  600,
  601,
  606,
  653,
  655,
  656,
  658,
  659,
  661,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(0, 1), (29, 1), (36, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (32, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (30, 1), (36, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := -2, powers := [(0, 1), (49, 1), (66, 1)] }, { coefficient := -2, powers := [(20, 1), (49, 1), (66, 1)] }, { coefficient := -2, powers := [(30, 1), (36, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (36, 1), (47, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (30, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (24, 1), (36, 1), (44, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (36, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1), (36, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (32, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (19, 1), (29, 1), (36, 1), (47, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (32, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (55, 1), (66, 1)] }, { coefficient := 2, powers := [(33, 1), (36, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (33, 1), (36, 1), (49, 1), (61, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (49, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (24, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (19, 1), (29, 1), (36, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (26, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(6, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(9, 1), (53, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (26, 1), (36, 1), (49, 1), (51, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (49, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (36, 1), (40, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (49, 1), (51, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(26, 1), (49, 1), (51, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (40, 1), (49, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (49, 1), (53, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(49, 1), (53, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (29, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (29, 1), (30, 1), (36, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (36, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (30, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (30, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (26, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (36, 1), (49, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (33, 1), (36, 1), (40, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (49, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(26, 1), (49, 1), (55, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (29, 1), (36, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (29, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (29, 1), (36, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (24, 1), (36, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (30, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (19, 1), (36, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(9, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (36, 1), (49, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (40, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(36, 1), (49, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(49, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (36, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (33, 1), (36, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (33, 1), (36, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (49, 1), (59, 1)] }, { coefficient := 2, powers := [(49, 1)] }],
  [{ coefficient := 2, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (33, 1), (36, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 2), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (36, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (30, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (30, 1), (36, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (18, 1), (24, 1), (26, 1), (36, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (55, 1)] }, { coefficient := 2, powers := [(6, 1), (33, 1)] }, { coefficient := -2, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (36, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (18, 1), (26, 1), (29, 1), (36, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (18, 1), (26, 1), (32, 1), (36, 1), (48, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (26, 1), (29, 1), (36, 1), (47, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (26, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := -2, powers := [(20, 1), (29, 1), (55, 1), (66, 1)] }, { coefficient := -2, powers := [(26, 1), (43, 1), (55, 1), (64, 1)] }, { coefficient := -2, powers := [(29, 1), (33, 1), (36, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (13, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (13, 1), (30, 1), (35, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (29, 1), (33, 1), (36, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (13, 1), (29, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (36, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (33, 1), (36, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(20, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (29, 1), (36, 1), (48, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (24, 1), (36, 1), (46, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (24, 1), (36, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (36, 1), (49, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (26, 1), (43, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (43, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(9, 1), (43, 1), (53, 1), (55, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (29, 1), (30, 1), (36, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(13, 1), (18, 1), (24, 1), (30, 1), (36, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (24, 1), (30, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (36, 1), (43, 1), (49, 1), (51, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (36, 1), (43, 1), (49, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (39, 1)] }, { coefficient := -1, powers := [(20, 1), (33, 1), (36, 1), (40, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (33, 1), (36, 1), (45, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (33, 1), (36, 1), (40, 1), (43, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (43, 1), (49, 1), (51, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(26, 1), (43, 1), (49, 1), (51, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (40, 1), (43, 1), (49, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(36, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(36, 1), (43, 1), (49, 1), (53, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(39, 1), (42, 1)] }, { coefficient := -2, powers := [(42, 1), (49, 1)] }, { coefficient := -2, powers := [(43, 1), (49, 1), (53, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (33, 1), (36, 1), (40, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (33, 1), (36, 1), (45, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := -2, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(20, 1), (33, 1), (36, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(20, 1), (42, 1), (49, 1)] }, { coefficient := 2, powers := [(30, 1), (36, 1), (42, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_5_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_5_3
