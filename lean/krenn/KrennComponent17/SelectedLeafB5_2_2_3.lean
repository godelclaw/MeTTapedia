import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_2_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7d191f912f054ca4292bf41f22bef9c6b19bb13f1a5e76b34cf496fb0f5b0f2c"
def certificateSHA256 : String := "1308ad6b0ca73e0980e75df0445ba4d7f8a5657873e679b60667eabe3eb65081"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 614 := ![
  11,
  12,
  25,
  35,
  137,
  187,
  191,
  197,
  204,
  308,
  309,
  312,
  314,
  322,
  365,
  393,
  431,
  455,
  468,
  490,
  509,
  549,
  557,
  567,
  568,
  570,
  571,
  599,
  600,
  603,
  604,
  605,
  606,
  608,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(11, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(0, 1), (9, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (27, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (27, 1), (60, 1)] }, { coefficient := -3, powers := [(19, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (22, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (27, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (22, 1), (48, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (27, 1), (48, 1), (60, 1), (63, 1)] }, { coefficient := -3, powers := [(0, 1), (22, 1), (36, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -3, powers := [(0, 1), (27, 1), (36, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (22, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (27, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (22, 1), (33, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (27, 1), (33, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (22, 1), (48, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (27, 1), (48, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (30, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (27, 1), (30, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(22, 1), (33, 1), (36, 1), (48, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (6, 1), (48, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (48, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (9, 1), (21, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (9, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (48, 1), (63, 1)] }, { coefficient := -3, powers := [(2, 1), (19, 1), (48, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1), (63, 1)] }, { coefficient := -2, powers := [(30, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (22, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 1), (26, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (31, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (34, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (21, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (14, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (33, 1), (36, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (11, 1), (50, 1), (61, 1)] }, { coefficient := -4, powers := [(9, 1), (11, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (9, 1), (33, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 1), (33, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(0, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (19, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (11, 1), (21, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 1), (34, 1)] }, { coefficient := -2, powers := [(9, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (21, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (48, 1), (60, 1)] }, { coefficient := 3, powers := [(0, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 3, powers := [(6, 1), (19, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (21, 1), (33, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (9, 1), (26, 1), (33, 1), (44, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (33, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (60, 1)] }, { coefficient := 3, powers := [(19, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (21, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1)] }, { coefficient := 2, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(42, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 1), (15, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (48, 1)] }, { coefficient := -3, powers := [(36, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(3, 1), (9, 1), (33, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 1), (33, 1), (37, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (33, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (33, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (48, 1)] }, { coefficient := -3, powers := [(0, 1), (36, 2), (56, 1), (57, 1)] }, { coefficient := -5, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (33, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 2), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -3, powers := [(19, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (24, 1), (44, 1)] }, { coefficient := 2, powers := [(6, 1), (33, 1)] }, { coefficient := 2, powers := [(14, 1), (19, 1), (29, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(14, 1), (24, 1)] }, { coefficient := -2, powers := [(17, 1), (26, 1), (27, 1), (33, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := -2, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (9, 1), (21, 1), (33, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (14, 1), (21, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (6, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (12, 1), (22, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (22, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (39, 1)] }, { coefficient := -3, powers := [(2, 1), (19, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (11, 1), (26, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (11, 1), (31, 1), (54, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (11, 1), (34, 1), (54, 1)] }, { coefficient := 2, powers := [(3, 1), (30, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (19, 1), (21, 1), (57, 1)] }, { coefficient := 4, powers := [(9, 1), (11, 1), (21, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1)] }, { coefficient := -3, powers := [(12, 1), (19, 1), (22, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (4, 1), (9, 1), (26, 1), (33, 1), (44, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (4, 1), (9, 1), (33, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (11, 1), (26, 1), (33, 1), (44, 2)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (11, 1), (33, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (15, 1), (26, 1), (33, 1), (40, 1), (44, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (15, 1), (33, 1), (34, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (48, 1), (57, 1)] }, { coefficient := 3, powers := [(3, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (21, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(9, 1), (11, 1), (14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (36, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (42, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 3, powers := [(36, 1), (56, 1)] }, { coefficient := -2, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (6, 1), (42, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (17, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (17, 1), (27, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (9, 1), (21, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (42, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (17, 1), (22, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (17, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 3, powers := [(0, 1), (17, 1), (22, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 3, powers := [(0, 1), (17, 1), (27, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 3, powers := [(2, 1), (19, 1), (42, 1), (48, 1), (60, 1)] }, { coefficient := 3, powers := [(6, 1), (17, 1), (19, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := 3, powers := [(6, 1), (17, 1), (19, 1), (27, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (17, 1), (21, 1), (22, 1), (33, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (17, 1), (21, 1), (27, 1), (33, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (19, 1), (22, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (19, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (22, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (27, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (33, 1), (36, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (14, 1), (19, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_2_2_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_2_2_3
