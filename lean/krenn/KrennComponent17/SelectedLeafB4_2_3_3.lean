import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_2_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ed0bddf98d69054443484b58d3120dd2d11505bc83732f159416cf603da077bb"
def certificateSHA256 : String := "0a730ac03c47694de72caf039cd26f0fc42e52400148f426af05f4477952d300"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 614 := ![
  30,
  35,
  36,
  187,
  294,
  300,
  306,
  308,
  309,
  312,
  314,
  326,
  357,
  358,
  365,
  417,
  423,
  425,
  447,
  454,
  456,
  490,
  549,
  567,
  568,
  570,
  571,
  572,
  599,
  600,
  602,
  603,
  605,
  608,
  610,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 4, powers := [(7, 1), (33, 1), (36, 1), (43, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := 4, powers := [(11, 1), (33, 1), (36, 1), (43, 1), (48, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 2), (9, 1), (57, 2), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (9, 1), (36, 1), (57, 2), (63, 1)] }, { coefficient := -4, powers := [(0, 1), (48, 1), (63, 1)] }, { coefficient := -4, powers := [(19, 1), (48, 1), (63, 1)] }, { coefficient := -4, powers := [(30, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (6, 1), (25, 1), (40, 1), (56, 1), (59, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (6, 1), (25, 1), (56, 1), (59, 2), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 2), (25, 1), (36, 1), (40, 1), (56, 1), (59, 1), (62, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 2), (25, 1), (36, 1), (56, 1), (59, 2), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (25, 1), (40, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (25, 1), (44, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (36, 1), (40, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (36, 1), (44, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -6, powers := [(6, 1), (25, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -4, powers := [(9, 1), (25, 1), (33, 1), (36, 1), (44, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -4, powers := [(26, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -4, powers := [(31, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := -4, powers := [(34, 1), (36, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (30, 1), (36, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (30, 1), (64, 1)] }],
  [{ coefficient := -4, powers := [(7, 1), (33, 1), (36, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := -4, powers := [(11, 1), (33, 1), (36, 1), (48, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (40, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (44, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (40, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (44, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -6, powers := [(6, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -4, powers := [(9, 1), (33, 1), (36, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(33, 1), (36, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -4, powers := [(33, 1), (36, 1), (44, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1)] }, { coefficient := -2, powers := [(19, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := -4, powers := [(6, 1), (33, 1), (36, 1), (57, 1), (64, 1)] }, { coefficient := -4, powers := [(19, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (6, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 2), (36, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (22, 1), (25, 1), (56, 1), (64, 2)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (30, 1), (36, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (36, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (22, 1), (25, 1), (36, 1), (56, 1), (64, 2)] }, { coefficient := -2, powers := [(6, 1), (14, 1), (19, 1), (30, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 2), (57, 2), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (36, 1), (57, 2), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 2), (56, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (25, 1), (28, 1), (56, 1), (64, 2)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (36, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (28, 1), (36, 1), (56, 1), (64, 2)] }],
  [{ coefficient := -4, powers := [(34, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -4, powers := [(22, 1), (33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (6, 1), (25, 1), (56, 1), (59, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (6, 1), (51, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 2), (25, 1), (36, 1), (56, 1), (59, 2), (62, 1)] }, { coefficient := -2, powers := [(0, 2), (36, 1), (51, 1), (56, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (28, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (28, 1), (36, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 4, powers := [(22, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (40, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (40, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 6, powers := [(6, 1), (56, 1), (62, 1)] }, { coefficient := 4, powers := [(9, 1), (33, 1), (36, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (22, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (22, 1), (36, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 4, powers := [(26, 1), (33, 1), (36, 1), (44, 1), (48, 1)] }, { coefficient := 4, powers := [(33, 1), (34, 1), (36, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (22, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (22, 1), (36, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(6, 1), (14, 1), (19, 1), (30, 1), (59, 1)] }, { coefficient := 4, powers := [(9, 1), (29, 1), (33, 1), (36, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := 4, powers := [(22, 1), (25, 1), (33, 1), (36, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 4, powers := [(48, 1)] }],
  [{ coefficient := 2, powers := [(14, 1)] }, { coefficient := 4, powers := [(42, 1)] }],
  [{ coefficient := -4, powers := [(15, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (14, 1), (30, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (6, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 2), (36, 1), (56, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -4, powers := [] }],
  [{ coefficient := 4, powers := [(33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (6, 1), (25, 1), (45, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (6, 1), (40, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 2), (25, 1), (36, 1), (45, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 2), (36, 1), (40, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (14, 1), (19, 1), (30, 1), (44, 1)] }, { coefficient := 2, powers := [(6, 1), (14, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (14, 1), (30, 1)] }],
  [{ coefficient := -4, powers := [(33, 1), (36, 1), (37, 1), (48, 1), (57, 1)] }, { coefficient := -4, powers := [(33, 1), (36, 1), (40, 1), (48, 1), (54, 1)] }, { coefficient := -4, powers := [(33, 1), (36, 1), (44, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 2), (14, 1), (26, 1), (57, 2), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (14, 1), (26, 1), (36, 1), (57, 2), (63, 1)] }, { coefficient := 4, powers := [(0, 1), (29, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := 4, powers := [(6, 1), (29, 1), (33, 1), (36, 1), (57, 1), (64, 1)] }, { coefficient := 4, powers := [(6, 1), (33, 1)] }, { coefficient := 2, powers := [(14, 1), (24, 1)] }, { coefficient := 4, powers := [(19, 1), (29, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := -4, powers := [(22, 1), (25, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := -4, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (9, 1)] }, { coefficient := 4, powers := [(0, 1), (39, 1)] }, { coefficient := 4, powers := [(3, 1), (30, 1)] }, { coefficient := 6, powers := [(9, 1), (19, 1)] }, { coefficient := 4, powers := [(11, 1), (26, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := 4, powers := [(11, 1), (31, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := 4, powers := [(11, 1), (34, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := -4, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (6, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 2), (6, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 2), (36, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 2), (36, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (36, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := -6, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 4, powers := [(7, 1), (21, 1), (33, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -4, powers := [(9, 1), (19, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 4, powers := [(11, 1), (21, 1), (33, 1), (36, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (6, 1), (25, 1), (40, 1), (43, 1), (56, 1), (59, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (6, 1), (25, 1), (45, 1), (56, 1), (59, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (6, 1), (40, 1), (43, 1), (51, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (6, 1), (45, 1), (51, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 2), (25, 1), (36, 1), (40, 1), (43, 1), (56, 1), (59, 2), (62, 1)] }, { coefficient := 2, powers := [(0, 2), (25, 1), (36, 1), (45, 1), (56, 1), (59, 2), (62, 1)] }, { coefficient := 2, powers := [(0, 2), (36, 1), (40, 1), (43, 1), (51, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 2), (36, 1), (45, 1), (51, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (22, 1), (40, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (22, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (40, 1), (43, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (43, 1), (44, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (22, 1), (36, 1), (40, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (22, 1), (36, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (40, 1), (43, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (43, 1), (44, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (6, 1), (14, 1), (30, 1), (57, 1), (59, 1)] }, { coefficient := 4, powers := [(3, 1), (56, 1)] }, { coefficient := -4, powers := [(4, 1), (26, 1), (33, 1), (36, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -4, powers := [(4, 1), (33, 1), (34, 1), (36, 1), (37, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (14, 1), (19, 1), (30, 1), (40, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (14, 1), (19, 1), (30, 1), (44, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (14, 1), (30, 1), (59, 1)] }, { coefficient := 6, powers := [(6, 1), (43, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (14, 1)] }, { coefficient := -4, powers := [(9, 1), (29, 1), (33, 1), (36, 1), (40, 1), (64, 1)] }, { coefficient := -4, powers := [(9, 1), (29, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := 4, powers := [(9, 1), (33, 1), (36, 1), (43, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -4, powers := [(11, 1), (26, 1), (33, 1), (36, 1), (44, 2), (48, 1)] }, { coefficient := -4, powers := [(11, 1), (33, 1), (34, 1), (36, 1), (37, 1), (44, 1), (48, 1)] }, { coefficient := -2, powers := [(14, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := -2, powers := [(14, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := -4, powers := [(15, 1), (26, 1), (33, 1), (36, 1), (40, 1), (44, 1), (48, 1)] }, { coefficient := -4, powers := [(15, 1), (33, 1), (34, 1), (36, 1), (37, 1), (40, 1), (48, 1)] }, { coefficient := -4, powers := [(22, 1), (25, 1), (33, 1), (36, 1), (40, 1), (49, 1), (64, 1)] }, { coefficient := -4, powers := [(22, 1), (25, 1), (33, 1), (36, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := -4, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (6, 1), (25, 1), (40, 1), (43, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (6, 1), (25, 1), (43, 1), (56, 1), (59, 2), (62, 1)] }, { coefficient := 2, powers := [(0, 2), (25, 1), (36, 1), (40, 1), (43, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 2), (25, 1), (36, 1), (43, 1), (56, 1), (59, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (6, 2), (56, 1), (57, 2)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (6, 1), (36, 1), (56, 1), (57, 2)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (25, 1), (40, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (25, 1), (43, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (36, 1), (40, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (36, 1), (43, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 4, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 6, powers := [(6, 1), (25, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := 4, powers := [(9, 1), (25, 1), (33, 1), (36, 1), (43, 1), (44, 1), (62, 1)] }, { coefficient := 4, powers := [(19, 1), (42, 1), (48, 1)] }, { coefficient := 4, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (6, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (6, 1), (44, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 2), (36, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 2), (36, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (6, 2), (56, 1), (57, 2)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (6, 1), (25, 1), (28, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (6, 1), (36, 1), (56, 1), (57, 2)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (25, 1), (28, 1), (36, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 2), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (19, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (19, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (22, 1), (25, 1), (40, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (22, 1), (25, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (25, 1), (28, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (36, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (22, 1), (25, 1), (36, 1), (40, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (22, 1), (25, 1), (36, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (28, 1), (36, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (14, 1), (19, 1), (30, 1), (44, 1)] }, { coefficient := 4, powers := [(9, 1), (19, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := -4, powers := [(9, 1), (33, 1), (36, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((4 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (4 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (4 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_2_3_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_2_3_3
