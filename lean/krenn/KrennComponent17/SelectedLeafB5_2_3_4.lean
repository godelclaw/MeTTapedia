import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_2_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e4b25664b3f11314dcc933416bbc324f364dfc304c0d7828bacaaafae00d35ee"
def certificateSHA256 : String := "9d3a940d1313d5b272163856607da02295dffac29e0783fa5803fb2131dec26d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 54 → Fin 614 := ![
  12,
  14,
  17,
  18,
  21,
  26,
  30,
  32,
  183,
  187,
  189,
  202,
  211,
  230,
  300,
  308,
  309,
  310,
  312,
  321,
  325,
  326,
  329,
  350,
  365,
  407,
  431,
  434,
  441,
  469,
  523,
  541,
  543,
  557,
  558,
  567,
  568,
  569,
  570,
  573,
  599,
  600,
  601,
  603,
  604,
  605,
  606,
  607,
  608,
  609,
  610,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 54 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 54 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (19, 1), (27, 1), (30, 1), (35, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (27, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (30, 1), (36, 1), (44, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (30, 1), (36, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (30, 1), (36, 1), (46, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (36, 1), (38, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (44, 1), (48, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (48, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(28, 1), (33, 1), (36, 1), (46, 1), (48, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (36, 1), (38, 1), (48, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (27, 1), (30, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1), (38, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (23, 1), (25, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (19, 1), (30, 1), (35, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 2), (35, 1), (36, 2)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (35, 1), (36, 1), (48, 2)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (33, 1), (35, 1), (36, 2), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (14, 1), (24, 1), (27, 1), (30, 1), (35, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (24, 1), (27, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (19, 1), (27, 1), (30, 1), (35, 1), (36, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (27, 1), (30, 2), (35, 1), (36, 2), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (27, 1), (33, 1), (35, 1), (36, 1), (48, 2), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (30, 1), (33, 1), (35, 1), (36, 2), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(27, 1), (30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (11, 1), (33, 1), (36, 1), (43, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (33, 1), (36, 1), (43, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (36, 1), (43, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (36, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (35, 1), (36, 2), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 1), (35, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (35, 1), (36, 2), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (42, 1), (48, 2)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (23, 1), (30, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (30, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1), (43, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (11, 1), (33, 1), (36, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (33, 1), (36, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (14, 1), (24, 1), (30, 1), (35, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (24, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (19, 1), (30, 1), (35, 1), (36, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 2), (35, 1), (36, 2), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (35, 1), (36, 1), (48, 2), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (33, 1), (35, 1), (36, 2), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (19, 1), (30, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (14, 1), (19, 1), (43, 1), (60, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (14, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (35, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (24, 1), (30, 1), (35, 1), (36, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (35, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (35, 1), (36, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (48, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (19, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (38, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (14, 1), (19, 1), (60, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (19, 1), (30, 1), (35, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (14, 1), (30, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (35, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (42, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (15, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (24, 1), (30, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (30, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (14, 1), (24, 1), (30, 1), (35, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (24, 1), (33, 1), (35, 1), (36, 1), (42, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (19, 1), (30, 1), (35, 1), (36, 2), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 2), (35, 1), (36, 2), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (35, 1), (36, 2), (48, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (33, 1), (35, 1), (36, 2), (42, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (14, 1), (30, 1), (33, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 2), (35, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (24, 1), (30, 1), (35, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (35, 1), (36, 1), (42, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (19, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (14, 1), (19, 1), (27, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (30, 1), (36, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (36, 1), (48, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (35, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (28, 1), (30, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (33, 1), (36, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (14, 1), (30, 1), (35, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (35, 1), (36, 1), (39, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (22, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (14, 1), (19, 1), (30, 1), (35, 1), (36, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (19, 1), (33, 1), (35, 1), (36, 1), (39, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (30, 2), (35, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (20, 1), (24, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (20, 1), (24, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (14, 1), (17, 1), (22, 1), (24, 1), (30, 1), (35, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (14, 1), (19, 1), (30, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (17, 1), (22, 1), (24, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (19, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (14, 1), (19, 1), (22, 1), (30, 1), (35, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (19, 1), (22, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (17, 1), (19, 1), (22, 1), (30, 1), (35, 1), (36, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (17, 1), (22, 1), (30, 2), (35, 1), (36, 2), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (19, 1), (22, 1), (33, 1), (35, 1), (36, 1), (48, 2), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (22, 1), (30, 1), (33, 1), (35, 1), (36, 2), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (11, 1), (21, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (31, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (34, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (34, 1), (36, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (30, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (11, 1), (21, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (21, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (19, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (14, 1), (23, 1), (30, 1), (36, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (23, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (28, 1), (30, 1), (36, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (35, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (33, 1), (36, 1), (44, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (33, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (33, 1), (36, 1), (46, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (35, 1), (36, 1), (38, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (33, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (43, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (19, 1), (43, 1), (44, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (19, 1), (45, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (36, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (36, 1), (43, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (30, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (36, 1), (41, 1), (48, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 54,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_2_3_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_2_3_4
