import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB6

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "094795ae442b7528aabb438da3d8d9d20980e4bd7ca215c338daf5ff07241741"
def sourceSystemSemanticSHA256 : String := "ff480499e9c9e0d64f196e3bd43d6a4dd3f51591ab1c2315aa45fd374af193fb"
def certificateSHA256 : String := "d7806a5ea4bd7681b9c6f2fcdfe8e8492018277246596c14ad6009d4f5fba418"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 66 → Fin 678 := ![
  0,
  1,
  25,
  26,
  28,
  29,
  31,
  32,
  33,
  35,
  36,
  40,
  43,
  47,
  48,
  310,
  322,
  384,
  407,
  416,
  418,
  419,
  420,
  421,
  422,
  423,
  424,
  425,
  426,
  429,
  439,
  441,
  460,
  500,
  503,
  507,
  518,
  531,
  538,
  559,
  605,
  606,
  613,
  615,
  622,
  624,
  626,
  633,
  635,
  640,
  641,
  643,
  645,
  650,
  657,
  659,
  663,
  665,
  666,
  671,
  672,
  673,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 66 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(36, 1), (69, 1)] }, { coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (38, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }, { coefficient := 1, powers := [(53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 66 → SparsePoly (Fin 72) := ![
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (7, 1), (47, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (13, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (24, 1), (25, 1), (32, 1), (35, 1), (39, 1), (59, 1), (70, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (28, 1), (32, 1), (35, 1), (39, 1), (59, 1), (70, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (24, 1), (37, 1), (44, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (43, 1), (44, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (44, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (32, 1), (37, 1), (41, 1), (58, 1), (66, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (32, 1), (37, 1), (41, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (32, 1), (41, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (34, 1), (40, 1), (44, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (40, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (43, 1), (46, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (14, 1), (24, 1), (25, 1), (32, 1), (35, 1), (39, 1), (45, 1), (70, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (37, 1), (44, 1), (69, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (43, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (26, 1), (32, 1), (37, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (26, 1), (32, 1), (37, 1), (41, 1), (66, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (32, 1), (37, 1), (41, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (32, 1), (41, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (34, 1), (40, 1), (44, 1), (57, 1)] }, { coefficient := 2, powers := [(13, 1), (32, 1), (43, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (28, 1), (32, 1), (35, 1), (39, 1), (45, 1), (70, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (33, 1), (35, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (24, 1), (31, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (32, 1), (43, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(15, 1), (24, 1), (31, 1), (40, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(15, 1), (32, 1), (40, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (31, 1), (37, 1), (44, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (34, 1), (37, 1), (43, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(32, 1), (34, 1), (35, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (3, 1), (32, 1), (38, 1), (40, 1), (58, 1), (60, 1), (71, 1)] }, { coefficient := -1, powers := [(1, 1), (32, 1), (38, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (38, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(15, 1), (32, 1), (38, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (41, 1), (51, 1), (52, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (24, 1), (33, 1), (37, 1), (44, 1), (49, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (37, 1), (44, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(21, 1), (32, 1), (37, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (33, 1), (37, 1), (44, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (17, 1), (23, 1), (24, 1), (25, 1), (33, 1), (36, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (23, 1), (24, 1), (33, 1), (38, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(9, 1), (17, 1), (24, 1), (25, 1), (31, 1), (33, 1), (36, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := 2, powers := [(9, 1), (17, 1), (24, 1), (31, 1), (33, 1), (38, 1), (40, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (24, 1), (26, 1), (33, 1), (37, 1), (44, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (26, 1), (33, 1), (37, 1), (44, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (24, 1), (33, 1), (35, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (24, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(32, 1), (37, 1), (40, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (25, 1), (33, 1), (36, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (33, 1), (38, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (31, 1), (33, 1), (36, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := -2, powers := [(24, 1), (31, 1), (33, 1), (38, 1), (40, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (21, 1), (24, 1), (37, 1), (44, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (24, 1), (43, 1), (44, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (32, 1), (37, 1), (41, 1), (69, 1)] }, { coefficient := -2, powers := [(13, 1), (32, 1), (37, 1), (43, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (38, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (38, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (24, 1), (31, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(15, 1), (21, 1), (32, 1), (43, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (31, 1), (38, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (34, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (31, 1), (37, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(21, 1), (32, 1), (37, 1), (43, 1), (46, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (21, 1), (24, 1), (25, 1), (32, 1), (35, 1), (39, 1), (70, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (28, 1), (32, 1), (35, 1), (39, 1), (70, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (32, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (32, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (31, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 2), (37, 1), (43, 1), (52, 1)] }, { coefficient := 2, powers := [(31, 1), (32, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (32, 1), (37, 1), (41, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (37, 1), (44, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (40, 1), (44, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (32, 1), (37, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (34, 1), (37, 1), (41, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (24, 1), (33, 1), (35, 1), (39, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (16, 1), (24, 1), (32, 1), (35, 1), (39, 1), (70, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (32, 1), (35, 1), (39, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (21, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (23, 1), (24, 1), (25, 1), (33, 1), (36, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(9, 1), (24, 1), (25, 1), (31, 1), (33, 1), (36, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (26, 1), (33, 1), (37, 1), (44, 1), (52, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (31, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (24, 1), (25, 1), (33, 1), (36, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (25, 1), (31, 1), (33, 1), (36, 1), (38, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (31, 1), (32, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(21, 1), (23, 1), (26, 1), (32, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (32, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (68, 1), (69, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1), (68, 1), (70, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1), (68, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (35, 1), (64, 1), (68, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (32, 1), (38, 1), (55, 1), (68, 1), (70, 1)] }, { coefficient := 2, powers := [(0, 1), (11, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (68, 1), (69, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1), (68, 1), (70, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (24, 1), (35, 1), (64, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (32, 1), (38, 1), (55, 1), (68, 1), (70, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1), (68, 1)] }, { coefficient := -2, powers := [(3, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (55, 1), (68, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1), (68, 1)] }, { coefficient := 2, powers := [(11, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (35, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (55, 1), (68, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (33, 1), (37, 1), (42, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (33, 1), (37, 1), (44, 1), (52, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (33, 1), (38, 1), (42, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(24, 1), (31, 1), (33, 1), (38, 1), (40, 1), (42, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (42, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (32, 1), (37, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (32, 1), (38, 1), (40, 1), (49, 1), (58, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (31, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(23, 1), (32, 1), (43, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (40, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(32, 1), (40, 1), (43, 1), (46, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (38, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(32, 1), (38, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (23, 1), (24, 1), (37, 1), (44, 1), (45, 1), (52, 1), (69, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (38, 1), (43, 1), (45, 1), (58, 1), (60, 1), (70, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (31, 1), (38, 1), (40, 1), (45, 1), (58, 1), (60, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (45, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (38, 1), (45, 1), (55, 1), (70, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (24, 1), (37, 1), (44, 1), (45, 1), (52, 1), (69, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (24, 1), (38, 1), (43, 1), (45, 1), (58, 1), (60, 1), (70, 1)] }, { coefficient := -2, powers := [(11, 1), (24, 1), (31, 1), (38, 1), (40, 1), (45, 1), (58, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (35, 1), (45, 1), (64, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (45, 1), (55, 1), (70, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (23, 1), (24, 1), (25, 1), (37, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (24, 1), (25, 1), (38, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(11, 1), (24, 1), (25, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (25, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (28, 1), (37, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (28, 1), (38, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(24, 1), (28, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (17, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(11, 1), (17, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (24, 1), (31, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (31, 1), (37, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (34, 1), (37, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (32, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (37, 1), (44, 1), (58, 1)] }, { coefficient := 2, powers := [(21, 1), (32, 1), (37, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (24, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (24, 1), (33, 1), (36, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (31, 1), (33, 1), (36, 1), (38, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (24, 1), (37, 1), (44, 1), (69, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (43, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(21, 1), (32, 1), (37, 1), (41, 1), (69, 1)] }, { coefficient := 2, powers := [(32, 1), (37, 1), (43, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (37, 1), (44, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(32, 1), (37, 1), (41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (26, 1), (32, 1), (37, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1), (32, 1), (35, 1), (39, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1), (24, 1), (33, 1), (36, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(9, 1), (24, 1), (31, 1), (33, 1), (36, 1), (38, 1), (40, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (24, 1), (33, 1), (37, 1), (44, 1), (52, 1), (56, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (33, 1), (37, 1), (44, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (24, 1), (25, 1), (32, 1), (35, 1), (39, 1), (70, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (32, 1), (35, 1), (39, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (32, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (24, 1), (31, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(21, 1), (32, 1), (43, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (38, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (40, 1), (46, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (32, 1), (37, 1), (41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (33, 1), (36, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(24, 1), (31, 1), (33, 1), (36, 1), (38, 1), (40, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (32, 1), (35, 1), (39, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(32, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (24, 1), (33, 1), (37, 1), (44, 1), (52, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (17, 1), (23, 1), (24, 1), (33, 1), (36, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (24, 1), (31, 1), (33, 1), (36, 1), (38, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (69, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1), (70, 1)] }, { coefficient := -2, powers := [(3, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (64, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (55, 1), (70, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (69, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1), (70, 1)] }, { coefficient := 2, powers := [(11, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (35, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (55, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (32, 1), (38, 1), (40, 1), (58, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (37, 1), (44, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (43, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (32, 1), (37, 1), (41, 1), (66, 1)] }, { coefficient := 2, powers := [(23, 1), (32, 1), (37, 1), (41, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (41, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := -2, powers := [(32, 1), (43, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(11, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (56, 1), (65, 1), (69, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (59, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (38, 1), (43, 1), (56, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (31, 1), (38, 1), (40, 1), (56, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (38, 1), (55, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (38, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (56, 1), (65, 1), (69, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (59, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (24, 1), (38, 1), (43, 1), (56, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (24, 1), (38, 1), (43, 1), (58, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(11, 1), (24, 1), (31, 1), (38, 1), (40, 1), (56, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(11, 1), (24, 1), (31, 1), (38, 1), (40, 1), (58, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (35, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (35, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (55, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (32, 1), (38, 1), (40, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (32, 1), (38, 1), (40, 1), (57, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (47, 1), (52, 1), (67, 2)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (47, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (53, 1), (67, 1), (68, 1), (69, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (24, 1), (38, 1), (43, 1), (53, 1), (58, 1), (60, 1), (67, 1), (68, 1), (70, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (24, 1), (31, 1), (38, 1), (40, 1), (53, 1), (58, 1), (60, 1), (67, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (24, 1), (35, 1), (53, 1), (64, 1), (67, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (32, 1), (38, 1), (53, 1), (55, 1), (67, 1), (68, 1), (70, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (53, 1), (67, 1), (68, 1), (69, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (23, 1), (24, 1), (38, 1), (43, 1), (53, 1), (58, 1), (60, 1), (67, 1), (68, 1), (70, 1)] }, { coefficient := 2, powers := [(0, 1), (11, 1), (24, 1), (31, 1), (38, 1), (40, 1), (53, 1), (58, 1), (60, 1), (67, 1), (68, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (24, 1), (35, 1), (53, 1), (64, 1), (67, 1), (68, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (32, 1), (38, 1), (53, 1), (55, 1), (67, 1), (68, 1), (70, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (53, 1), (67, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (38, 1), (43, 1), (53, 1), (58, 1), (60, 1), (67, 1), (68, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (31, 1), (38, 1), (40, 1), (53, 1), (58, 1), (60, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (53, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (38, 1), (53, 1), (55, 1), (67, 1), (68, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (53, 1), (67, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (24, 1), (38, 1), (43, 1), (53, 1), (58, 1), (60, 1), (67, 1), (68, 1)] }, { coefficient := -2, powers := [(11, 1), (24, 1), (31, 1), (38, 1), (40, 1), (53, 1), (58, 1), (60, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (35, 1), (53, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (53, 1), (55, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (31, 1), (41, 1), (51, 1), (54, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (44, 1), (55, 1), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(21, 1), (32, 1), (43, 1), (46, 1), (54, 1), (55, 1), (67, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (33, 1), (37, 1), (42, 1), (44, 1), (52, 1), (53, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (33, 1), (37, 1), (44, 1), (52, 1), (53, 1), (56, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (33, 1), (38, 1), (42, 1), (43, 1), (53, 1), (58, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (37, 1), (44, 1), (55, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (43, 1), (44, 1), (52, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (43, 1), (44, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (44, 1), (51, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (44, 1), (51, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (32, 1), (37, 1), (41, 1), (52, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (32, 1), (37, 1), (41, 1), (55, 1), (64, 1), (66, 1)] }, { coefficient := -2, powers := [(23, 1), (32, 1), (37, 1), (41, 1), (52, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(23, 1), (32, 1), (37, 1), (41, 1), (55, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (43, 1), (52, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (43, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(24, 1), (31, 1), (33, 1), (38, 1), (40, 1), (42, 1), (53, 1), (58, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (38, 1), (51, 1), (54, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (42, 1), (53, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (38, 1), (43, 1), (54, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (40, 1), (44, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (40, 1), (44, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (46, 1), (57, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (46, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (46, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(32, 1), (41, 1), (52, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 2, powers := [(32, 1), (43, 1), (46, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := 2, powers := [(32, 1), (43, 1), (46, 1), (54, 1), (55, 1), (64, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly]
  ring

theorem selectedHasNoCommonZero {R : Type*}
    [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 66,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case64Tree.LeafB6.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB6
