import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2519407a9478beaee1c255ddcb47592f88eadd42424711c5caf8b8c6b229ae22"
def certificateSHA256 : String := "cbffd46b460e4f8e6da6b0506f144c7af67c4ee605d97260ec722364c40e048b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 614 := ![
  12,
  25,
  30,
  35,
  36,
  56,
  187,
  197,
  300,
  306,
  308,
  309,
  312,
  357,
  365,
  427,
  431,
  445,
  454,
  455,
  468,
  490,
  549,
  553,
  557,
  567,
  568,
  570,
  571,
  599,
  600,
  603,
  604,
  606,
  608,
  610,
  611,
  612
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 67) := ![
  [{ coefficient := -2, powers := [(0, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (27, 1), (50, 1), (56, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (27, 1), (54, 1), (56, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (28, 1), (56, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (22, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (27, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (27, 1), (50, 1), (56, 1), (60, 1), (62, 2), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (27, 1), (54, 1), (56, 1), (60, 1), (62, 2), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (28, 1), (56, 1), (60, 1), (62, 2), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (22, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (27, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (30, 1), (36, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (27, 1), (30, 1), (36, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(22, 1), (33, 1), (36, 1), (48, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (43, 1), (50, 1), (56, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (43, 1), (54, 1), (56, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (43, 1), (50, 1), (56, 1), (62, 2), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (43, 1), (54, 1), (56, 1), (62, 2), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (33, 1), (36, 1), (43, 1), (57, 1), (64, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (33, 1), (36, 1), (43, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (48, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1), (65, 1)] }, { coefficient := -2, powers := [(30, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -3, powers := [(6, 1), (25, 1), (56, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (31, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (34, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (31, 1), (60, 1), (62, 2), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (34, 1), (60, 1), (62, 2), (65, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (26, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(9, 1), (31, 1), (36, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (33, 1), (36, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (50, 1), (56, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (54, 1), (56, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (50, 1), (56, 1), (62, 2), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (54, 1), (56, 1), (62, 2), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (33, 1), (36, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(9, 1), (11, 1), (33, 1), (36, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -3, powers := [(6, 1), (51, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (33, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (33, 1), (36, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(0, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (34, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (56, 1), (60, 1), (62, 2)] }],
  [{ coefficient := -2, powers := [(33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (27, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (27, 1), (56, 1), (60, 1), (62, 2)] }],
  [{ coefficient := 3, powers := [(6, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (26, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := -2, powers := [(9, 1), (33, 1), (34, 1), (36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(42, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (56, 1), (62, 2), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (15, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(9, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (33, 1), (36, 1), (37, 1), (57, 1)] }, { coefficient := 2, powers := [(9, 1), (33, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (33, 1), (36, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (31, 1), (37, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (34, 1), (37, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (31, 1), (37, 1), (56, 1), (62, 2), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (34, 1), (37, 1), (56, 1), (62, 2), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (44, 1), (56, 1), (62, 2)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 2), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := 2, powers := [(33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (22, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (39, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (39, 1)] }, { coefficient := 2, powers := [(3, 1), (30, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (26, 1), (36, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (31, 1), (36, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := 3, powers := [(9, 1), (19, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1)] }, { coefficient := -2, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (21, 1), (50, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (21, 1), (54, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (21, 1), (50, 1), (56, 1), (62, 2), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (21, 1), (54, 1), (56, 1), (62, 2), (65, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (21, 1), (33, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (9, 1), (26, 1), (33, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (9, 1), (33, 1), (34, 1), (36, 1), (37, 1), (57, 1)] }, { coefficient := 3, powers := [(6, 1), (43, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(9, 1), (11, 1), (26, 1), (33, 1), (36, 1), (44, 2)] }, { coefficient := 2, powers := [(9, 1), (11, 1), (33, 1), (34, 1), (36, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(9, 1), (15, 1), (26, 1), (33, 1), (36, 1), (40, 1), (44, 1)] }, { coefficient := 2, powers := [(9, 1), (15, 1), (33, 1), (34, 1), (36, 1), (37, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := -2, powers := [(14, 1), (39, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := -2, powers := [(39, 1), (42, 1)] }, { coefficient := -2, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (17, 1), (27, 1), (50, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (17, 1), (27, 1), (54, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (17, 1), (28, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (40, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (17, 1), (22, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (17, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (27, 1), (50, 1), (56, 1), (60, 1), (62, 2)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (27, 1), (54, 1), (56, 1), (60, 1), (62, 2)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (28, 1), (56, 1), (60, 1), (62, 2)] }, { coefficient := -2, powers := [(3, 1), (40, 1), (56, 1), (62, 2)] }, { coefficient := -2, powers := [(3, 1), (44, 1), (56, 1), (62, 2)] }, { coefficient := 2, powers := [(3, 1), (56, 1), (62, 1)] }, { coefficient := 3, powers := [(6, 1), (25, 1), (43, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (19, 1), (22, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (19, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (22, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (27, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := 2, powers := [(14, 1), (39, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (33, 1), (36, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (33, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(30, 1), (36, 1), (42, 1)] }]
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

#print axioms Krenn.Component17.SelectedLeafB5_6_3_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_3_3
