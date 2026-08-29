import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f0f19d2972a72189b986f64d357ddbd2997b993ca3f31b4018ca1723822d800b"
def certificateSHA256 : String := "4f75f0c80874ffef5901a5c08186e51bc95577b47822a350e5d2c2ade51a4105"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 48 → Fin 614 := ![
  11,
  12,
  25,
  29,
  35,
  65,
  137,
  187,
  191,
  197,
  204,
  294,
  308,
  309,
  312,
  314,
  322,
  326,
  336,
  357,
  365,
  389,
  393,
  405,
  431,
  435,
  455,
  468,
  490,
  497,
  504,
  509,
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
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 48 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(11, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (50, 1)] }],
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
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 48 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(0, 1), (9, 1), (21, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (27, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (27, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (27, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := -3, powers := [(19, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (22, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (27, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -3, powers := [(0, 1), (22, 1), (36, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := -3, powers := [(0, 1), (27, 1), (36, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (22, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (27, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(3, 1), (22, 1), (56, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(3, 1), (27, 1), (56, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (22, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (27, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (22, 1), (33, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (27, 1), (33, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (22, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (27, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (30, 1), (36, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (27, 1), (30, 1), (36, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(22, 1), (33, 1), (36, 1), (48, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (7, 1), (14, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (9, 1), (21, 1), (57, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (9, 1), (34, 1), (44, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (9, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (48, 1), (64, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (19, 1), (48, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (48, 1), (57, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -3, powers := [(2, 1), (19, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (64, 1)] }, { coefficient := 2, powers := [(9, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1), (64, 1)] }, { coefficient := -2, powers := [(30, 1), (36, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (34, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (26, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (31, 1), (36, 1), (44, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (31, 1), (36, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (34, 1), (36, 1), (44, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (34, 1), (36, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (22, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (31, 1), (36, 1), (44, 1), (49, 1)] }, { coefficient := -2, powers := [(0, 1), (34, 1), (36, 1), (44, 1), (49, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (26, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (31, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (34, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (21, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (14, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (33, 1), (36, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (7, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (50, 1), (62, 1)] }, { coefficient := -4, powers := [(9, 1), (11, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (7, 1), (31, 1), (48, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (34, 1), (39, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (40, 1), (48, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (33, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (4, 1), (26, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (31, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (21, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (31, 1), (40, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (31, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (34, 1), (40, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (26, 1), (40, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (26, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (19, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (11, 1), (21, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (7, 1), (14, 1), (31, 1), (48, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (14, 1), (34, 1), (39, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (7, 1), (34, 1), (44, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (64, 1)] }, { coefficient := -2, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 1), (34, 1)] }, { coefficient := -2, powers := [(9, 1), (21, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := -2, powers := [(0, 1), (34, 1), (37, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (11, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (4, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (48, 1), (60, 1)] }, { coefficient := 3, powers := [(0, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 3, powers := [(6, 1), (19, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (21, 1), (33, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (26, 1), (44, 1), (48, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (34, 1), (37, 1), (48, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (26, 1), (33, 1), (44, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (33, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (36, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (34, 1), (36, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (7, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 3, powers := [(19, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (21, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1)] }, { coefficient := 2, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(42, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (11, 1), (14, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (15, 1), (48, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (15, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (48, 1)] }, { coefficient := -3, powers := [(36, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (48, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (33, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (40, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (50, 2), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (37, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (40, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (40, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (48, 1), (50, 2)] }, { coefficient := 2, powers := [(0, 1), (37, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (33, 1), (37, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (33, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (33, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (48, 1)] }, { coefficient := -3, powers := [(0, 1), (36, 2), (56, 1), (57, 1)] }, { coefficient := -5, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (56, 1), (62, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (21, 1), (33, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 2), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -3, powers := [(19, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (21, 1), (33, 1)] }, { coefficient := -2, powers := [(9, 1), (11, 1), (14, 1), (21, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (9, 1), (26, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (9, 1), (31, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (9, 1), (21, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (9, 1), (31, 1), (40, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (9, 1), (31, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (9, 1), (34, 1), (40, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (21, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (11, 1), (26, 1), (40, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (11, 1), (26, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (19, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (19, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (11, 1), (31, 1), (36, 1), (44, 1), (49, 1)] }, { coefficient := 2, powers := [(0, 1), (11, 1), (34, 1), (36, 1), (44, 1), (49, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (22, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (15, 1), (21, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (15, 1), (21, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (39, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (39, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (19, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (39, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := -3, powers := [(2, 1), (19, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (11, 1), (26, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (11, 1), (31, 1), (54, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (11, 1), (34, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (19, 1), (22, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (22, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (30, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (19, 1), (21, 1), (57, 1)] }, { coefficient := 4, powers := [(9, 1), (11, 1), (21, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1)] }, { coefficient := -3, powers := [(12, 1), (19, 1), (22, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1)] }, { coefficient := -2, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (4, 1), (14, 1), (26, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (14, 1), (34, 1), (37, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (31, 1), (37, 1), (42, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (34, 1), (37, 1), (42, 1), (44, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (14, 1), (26, 1), (44, 2), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (14, 1), (34, 1), (37, 1), (44, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (15, 1), (26, 1), (40, 1), (44, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (15, 1), (34, 1), (37, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (39, 1), (44, 1)] }, { coefficient := -2, powers := [(3, 1), (4, 1), (9, 1), (26, 1), (33, 1), (44, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (4, 1), (9, 1), (33, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (11, 1), (26, 1), (33, 1), (44, 2)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (11, 1), (33, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (15, 1), (26, 1), (33, 1), (40, 1), (44, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (15, 1), (33, 1), (34, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (48, 1), (57, 1)] }, { coefficient := 3, powers := [(3, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (21, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(9, 1), (11, 1), (14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (36, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (42, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := -2, powers := [(14, 1), (39, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 3, powers := [(36, 1), (56, 1)] }, { coefficient := -2, powers := [(39, 1), (42, 1)] }, { coefficient := -2, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (7, 1), (34, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (9, 1), (21, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (14, 1), (34, 1), (39, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (42, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (17, 1), (22, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (17, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 3, powers := [(0, 1), (17, 1), (22, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 3, powers := [(0, 1), (17, 1), (27, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (19, 1), (42, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (42, 1), (48, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 3, powers := [(2, 1), (19, 1), (42, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (19, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (19, 1), (27, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (22, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (27, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (56, 1), (62, 1)] }, { coefficient := 3, powers := [(6, 1), (17, 1), (19, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := 3, powers := [(6, 1), (17, 1), (19, 1), (27, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (17, 1), (21, 1), (22, 1), (33, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (17, 1), (21, 1), (27, 1), (33, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (19, 1), (22, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (19, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (22, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (27, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := -2, powers := [(14, 1), (19, 1), (39, 1)] }, { coefficient := 2, powers := [(14, 1), (39, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (33, 1), (36, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (33, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (4, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (6, 1), (26, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (26, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (31, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (31, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (34, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (34, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (14, 1), (31, 1), (44, 1), (48, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (14, 1), (34, 1), (39, 1), (44, 1)] }, { coefficient := 2, powers := [(9, 1), (14, 1), (19, 1)] }, { coefficient := 2, powers := [(14, 1), (19, 1), (39, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 48,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_2_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_2_3
