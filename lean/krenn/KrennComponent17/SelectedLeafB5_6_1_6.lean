import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e5d88611de44688764e982ef3d3a544007ab0560482ee0877a723db9bd6f759f"
def certificateSHA256 : String := "2fb3a34ced030468bd477f7ce6d6cd42c9be97832a9ed48298171e74f6f2a847"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 614 := ![
  12,
  25,
  30,
  35,
  36,
  56,
  187,
  300,
  306,
  309,
  312,
  322,
  357,
  365,
  405,
  427,
  432,
  445,
  448,
  454,
  458,
  468,
  544,
  549,
  550,
  553,
  554,
  557,
  567,
  568,
  569,
  570,
  571,
  594,
  599,
  600,
  602,
  603,
  604,
  605,
  606,
  608,
  609,
  610,
  611,
  612
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (27, 1), (30, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (27, 1), (30, 1), (50, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (22, 1), (50, 1), (60, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (22, 1), (60, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (27, 1), (60, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (28, 1), (60, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (22, 1), (30, 1), (36, 1), (49, 1), (50, 1), (60, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (28, 1), (30, 1), (36, 1), (49, 1), (60, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (22, 1), (49, 1), (60, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (49, 1), (60, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (39, 1), (50, 1), (60, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (39, 1), (60, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (39, 1), (50, 1), (60, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (39, 1), (60, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (28, 1), (39, 1), (60, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (30, 1), (33, 1), (36, 1), (37, 1), (43, 1), (49, 1), (57, 1), (61, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (30, 1), (37, 1), (48, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (30, 1), (40, 1), (48, 1), (60, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (30, 1), (48, 1), (50, 1), (60, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (30, 1), (37, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (30, 1), (37, 1), (48, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (30, 1), (37, 1), (39, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (30, 1), (37, 1), (48, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 2), (36, 1), (37, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (24, 1), (44, 1), (51, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (25, 1), (44, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (30, 1), (37, 1), (51, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (40, 1), (49, 1), (51, 1), (61, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (49, 1), (51, 1), (59, 1), (61, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (49, 1), (51, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (30, 1), (37, 1), (59, 1), (61, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (30, 1), (37, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (40, 1), (49, 1), (61, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (49, 1), (59, 1), (61, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (49, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (24, 1), (30, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (19, 1), (30, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (30, 1), (36, 1), (37, 1), (49, 1), (57, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (30, 1), (33, 1), (36, 1), (37, 1), (49, 1), (57, 1), (61, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (44, 1), (51, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (37, 1), (51, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (49, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (51, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (51, 1), (61, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (33, 1), (36, 1), (37, 1), (44, 1), (49, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (36, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (36, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (26, 1), (30, 1), (36, 1), (44, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (30, 1), (34, 1), (36, 1), (37, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (36, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (36, 1), (49, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (37, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (34, 1), (36, 1), (37, 1), (49, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (30, 1), (36, 1), (49, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (30, 1), (36, 1), (49, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (30, 1), (36, 1), (44, 1), (49, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (30, 1), (36, 1), (49, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (39, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (44, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (37, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (49, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (61, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (49, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (60, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (49, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (37, 1), (39, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (30, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (30, 1), (50, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (37, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (37, 1), (42, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (26, 1), (30, 1), (36, 1), (44, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (30, 1), (34, 1), (36, 1), (37, 1), (49, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (14, 1), (30, 1), (36, 1), (49, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (14, 1), (30, 1), (36, 1), (49, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (14, 1), (30, 1), (36, 1), (44, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (30, 1), (33, 1), (36, 1), (37, 1), (49, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (33, 1), (36, 1), (37, 1), (49, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (33, 1), (36, 1), (37, 2), (49, 1), (57, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (30, 1), (37, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (37, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (30, 1), (37, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (30, 1), (36, 1), (40, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (30, 1), (36, 1), (50, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (36, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (30, 1), (36, 1), (49, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (36, 1), (49, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (49, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (39, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (30, 1), (33, 1), (37, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (24, 1), (30, 1), (37, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (30, 1), (36, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (30, 1), (37, 1), (39, 1), (40, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (30, 1), (37, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (30, 1), (39, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (30, 1), (39, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 2), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (22, 1), (30, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (22, 1), (30, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (19, 1), (30, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (30, 1), (36, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (30, 1), (36, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (26, 1), (30, 1), (36, 1), (37, 1), (49, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (30, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (37, 1), (39, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (39, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (39, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (39, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (39, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (39, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (30, 1), (33, 1), (36, 1), (37, 1), (40, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (36, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (14, 1), (21, 1), (30, 1), (36, 1), (49, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (30, 1), (31, 1), (33, 1), (36, 1), (37, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (14, 1), (21, 1), (30, 1), (36, 1), (49, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (22, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (19, 1), (36, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (19, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (19, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (19, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (14, 1), (21, 1), (30, 1), (36, 1), (44, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (14, 1), (26, 1), (30, 1), (36, 1), (44, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (14, 1), (30, 1), (34, 1), (36, 1), (37, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (21, 1), (30, 1), (33, 1), (36, 1), (37, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (17, 1), (22, 1), (30, 1), (36, 1), (49, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (21, 1), (30, 1), (33, 1), (36, 1), (37, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (27, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (21, 1), (30, 1), (33, 1), (36, 1), (37, 1), (49, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (19, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (30, 1), (37, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (40, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (49, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (49, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (49, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (40, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (44, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (30, 1), (37, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (30, 1), (40, 1), (42, 1), (48, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (30, 1), (42, 1), (48, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (37, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (22, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (22, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (27, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (24, 1), (43, 1), (44, 1), (51, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (25, 1), (43, 1), (44, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (17, 1), (22, 1), (30, 1), (36, 1), (49, 1), (50, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (17, 1), (28, 1), (30, 1), (36, 1), (49, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (30, 1), (37, 1), (39, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (19, 1), (22, 1), (49, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (19, 1), (27, 1), (49, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (39, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (39, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (27, 1), (39, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (27, 1), (39, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (28, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (30, 1), (37, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (30, 1), (37, 1), (39, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (30, 1), (37, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (30, 1), (37, 1), (43, 1), (51, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (40, 1), (43, 1), (49, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (43, 1), (49, 1), (51, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (43, 1), (49, 1), (51, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (30, 1), (37, 1), (43, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (30, 1), (37, 1), (43, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (40, 1), (43, 1), (49, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (43, 1), (49, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (43, 1), (49, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 2), (36, 1), (37, 1), (42, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_1_6.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_1_6
