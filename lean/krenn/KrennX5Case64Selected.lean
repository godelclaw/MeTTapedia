import KrennX5Case64Tree.LeafB0
import KrennX5Case64Tree.LeafB1_0
import KrennX5Case64Tree.LeafB1_1
import KrennX5Case64Tree.LeafB1_2
import KrennX5Case64Tree.LeafB1_3
import KrennX5Case64Tree.LeafB1_4
import KrennX5Case64Tree.LeafB1_5
import KrennX5Case64Tree.LeafB1_6
import KrennX5Case64Tree.LeafB1_7
import KrennX5Case64Tree.LeafB2
import KrennX5Case64Tree.LeafB3
import KrennX5Case64Tree.LeafB4
import KrennX5Case64Tree.LeafB5_0
import KrennX5Case64Tree.LeafB5_1
import KrennX5Case64Tree.LeafB5_2
import KrennX5Case64Tree.LeafB5_3
import KrennX5Case64Tree.LeafB5_4
import KrennX5Case64Tree.LeafB5_5
import KrennX5Case64Tree.LeafB5_6
import KrennX5Case64Tree.LeafB5_7
import KrennX5Case64Tree.LeafB6
import KrennX5Case64Tree.LeafB7_0
import KrennX5Case64Tree.LeafB7_1
import KrennX5Case64Tree.LeafB7_2
import KrennX5Case64Tree.LeafB7_3
import KrennX5Case64Tree.LeafB7_4
import KrennX5Case64Tree.LeafB7_5
import KrennX5Case64Tree.LeafB7_6
import KrennX5Case64Tree.LeafB7_7

namespace Krenn.X5Case64Selected

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedIndices : Fin 116 → Fin 675 := ![
  0,
  1,
  9,
  12,
  15,
  16,
  17,
  18,
  24,
  25,
  26,
  27,
  28,
  29,
  30,
  31,
  32,
  33,
  34,
  35,
  36,
  40,
  43,
  44,
  45,
  46,
  47,
  48,
  50,
  51,
  52,
  307,
  310,
  322,
  359,
  361,
  384,
  396,
  397,
  398,
  400,
  405,
  406,
  407,
  412,
  416,
  417,
  418,
  419,
  420,
  421,
  422,
  423,
  424,
  425,
  426,
  427,
  428,
  429,
  433,
  434,
  439,
  441,
  442,
  460,
  500,
  503,
  507,
  509,
  518,
  531,
  535,
  538,
  554,
  556,
  559,
  568,
  581,
  582,
  605,
  606,
  613,
  615,
  617,
  619,
  620,
  622,
  624,
  626,
  627,
  629,
  631,
  633,
  635,
  636,
  638,
  640,
  641,
  642,
  643,
  645,
  650,
  657,
  658,
  659,
  660,
  662,
  663,
  664,
  665,
  666,
  669,
  671,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedEquations : Fin 116 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (68, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(36, 1), (69, 1)] }, { coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (59, 1)] }, { coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (35, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (38, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }, { coefficient := 1, powers := [(53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

def RootSelectedZero {R : Type*} [CommRing R]
    (values : Fin 70 → R) : Prop :=
  ∀ index : Fin 116,
    eval₂Hom (Int.castRingHom R) values
      (rootSelectedEquations index).toPoly = 0

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Frozen compatibility and contradiction for terminal chart `b0`. -/
theorem leafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  let values1 : Fin 70 → R := values
  apply Krenn.X5Case64Tree.LeafB0.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨70, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨78, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨79, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨81, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨89, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨110, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b1.0`. -/
theorem leafB10Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 71 → R := values1
  apply Krenn.X5Case64Tree.LeafB1_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨110, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b1.1`. -/
theorem leafB11Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB1_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨103, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1.2`. -/
theorem leafB12Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case64Tree.LeafB1_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b1.3`. -/
theorem leafB13Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB1_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨57, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨63, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1.4`. -/
theorem leafB14Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case64Tree.LeafB1_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨73, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1.5`. -/
theorem leafB15Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB1_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨78, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨98, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b1.6`. -/
theorem leafB16Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case64Tree.LeafB1_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨74, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨97, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b1.7`. -/
theorem leafB17Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else if at1 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB1_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b2`. -/
theorem leafB2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  apply Krenn.X5Case64Tree.LeafB2.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨63, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨81, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨98, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b3`. -/
theorem leafB3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.X5Case64Tree.LeafB3.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨101, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨103, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨108, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨110, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4`. -/
theorem leafB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  apply Krenn.X5Case64Tree.LeafB4.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨66, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨70, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨75, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨79, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨81, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨83, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨88, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨91, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨96, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨100, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨102, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨104, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b5.0`. -/
theorem leafB50Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 72 → R := values1
  apply Krenn.X5Case64Tree.LeafB5_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨108, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨110, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b5.1`. -/
theorem leafB51Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB5_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨78, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨98, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b5.2`. -/
theorem leafB52Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case64Tree.LeafB5_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨104, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b5.3`. -/
theorem leafB53Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB5_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b5.4`. -/
theorem leafB54Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case64Tree.LeafB5_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨73, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨104, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b5.5`. -/
theorem leafB55Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB5_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨78, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨98, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b5.6`. -/
theorem leafB56Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case64Tree.LeafB5_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨74, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨97, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b5.7`. -/
theorem leafB57Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else if at1 : index.val = 73 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB5_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6`. -/
theorem leafB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  apply Krenn.X5Case64Tree.LeafB6.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨64, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨66, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨70, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨72, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨75, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨79, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨80, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨81, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨82, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨87, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨88, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨96, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨97, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨100, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨101, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨102, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨104, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨107, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨110, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case64Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b7.0`. -/
theorem leafB70Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 73 → R := values1
  apply Krenn.X5Case64Tree.LeafB7_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨108, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨110, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b7.1`. -/
theorem leafB71Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB7_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨78, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨98, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b7.2`. -/
theorem leafB72Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case64Tree.LeafB7_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨104, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b7.3`. -/
theorem leafB73Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 73 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB7_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b7.4`. -/
theorem leafB74Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case64Tree.LeafB7_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨73, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨104, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b7.5`. -/
theorem leafB75Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 73 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB7_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨78, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨98, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b7.6`. -/
theorem leafB76Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 73 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case64Tree.LeafB7_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨74, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨97, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b7.7`. -/
theorem leafB77Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 76 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 73 then
      d1Inverse0
    else if at1 : index.val = 74 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case64Tree.LeafB7_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case64Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Exhaustive reflection for carrier chart `b1`. -/
theorem nodeB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB10Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB11Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB12Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB13Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB14Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB15Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB16Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB17Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b5`. -/
theorem nodeB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB50Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB51Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB52Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB53Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB54Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB55Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB56Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB57Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b7`. -/
theorem nodeB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB70Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB71Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB72Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB73Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB74Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB75Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB76Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB77Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `root`. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    : False := by
  by_cases zeroD0C0 : values 0 = 0
  ·
    by_cases zeroD0C1 : values 3 = 0
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact leafB0Impossible values rootZero zeroD0C0 zeroD0C1 zeroD0C2
      ·
        exact nodeB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 7)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact leafB2Impossible values rootZero zeroD0C0 (values 3)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      ·
        exact leafB3Impossible values rootZero zeroD0C0 (values 3)⁻¹ (by simp [zeroD0C1]) (values 7)⁻¹ (by simp [zeroD0C2])
  ·
    by_cases zeroD0C1 : values 3 = 0
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact leafB4Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 zeroD0C2
      ·
        exact nodeB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 7)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact leafB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 3)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      ·
        exact nodeB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 3)⁻¹ (by simp [zeroD0C1]) (values 7)⁻¹ (by simp [zeroD0C2])

theorem selectedHasNoCommonZero (values : Fin 70 → ℂ) :
    ¬ RootSelectedZero values := by
  intro rootZero
  exact rootImpossible values rootZero

#print axioms Krenn.X5Case64Selected.selectedHasNoCommonZero

end Krenn.X5Case64Selected
