import KrennX5Case52Tree.LeafB0
import KrennX5Case52Tree.LeafB1
import KrennX5Case52Tree.LeafB2
import KrennX5Case52Tree.LeafB3
import KrennX5Case52Tree.LeafB4
import KrennX5Case52Tree.LeafB5
import KrennX5Case52Tree.LeafB6
import KrennX5Case52Tree.LeafB7

namespace Krenn.X5Case52Selected

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedIndices : Fin 117 → Fin 675 := ![
  0,
  1,
  8,
  9,
  11,
  12,
  15,
  16,
  18,
  20,
  23,
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
  38,
  39,
  40,
  43,
  44,
  45,
  46,
  47,
  48,
  50,
  53,
  199,
  302,
  307,
  310,
  311,
  320,
  342,
  343,
  349,
  350,
  353,
  395,
  397,
  398,
  403,
  405,
  406,
  412,
  414,
  416,
  417,
  419,
  420,
  421,
  422,
  423,
  424,
  425,
  426,
  427,
  433,
  434,
  436,
  440,
  442,
  447,
  460,
  463,
  467,
  468,
  469,
  475,
  500,
  503,
  531,
  534,
  535,
  559,
  568,
  581,
  582,
  587,
  590,
  593,
  595,
  615,
  617,
  619,
  620,
  623,
  624,
  627,
  629,
  640,
  641,
  642,
  643,
  649,
  650,
  651,
  658,
  659,
  660,
  661,
  662,
  664,
  665,
  666,
  667,
  671,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedEquations : Fin 117 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (53, 1)] }],
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
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(36, 1), (69, 1)] }, { coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (59, 1)] }, { coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }, { coefficient := 1, powers := [(53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

def RootSelectedZero {R : Type*} [CommRing R]
    (values : Fin 70 → R) : Prop :=
  ∀ index : Fin 117,
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
  apply Krenn.X5Case52Tree.LeafB0.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨88, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨116, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b1`. -/
theorem leafB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  apply Krenn.X5Case52Tree.LeafB1.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨57, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨101, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨103, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨104, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨107, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨112, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨116, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

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
  apply Krenn.X5Case52Tree.LeafB2.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨57, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨63, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨64, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨66, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨70, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨72, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨73, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨74, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨75, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨78, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨79, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨80, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨81, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨82, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨83, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨87, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨88, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨89, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨91, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨96, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨98, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨102, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨103, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨110, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨116, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

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
  apply Krenn.X5Case52Tree.LeafB3.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨57, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨66, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨74, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨80, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨82, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨83, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨96, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨102, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨103, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨104, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨105, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨107, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨114, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨116, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

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
  apply Krenn.X5Case52Tree.LeafB4.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨100, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨116, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b5`. -/
theorem leafB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  apply Krenn.X5Case52Tree.LeafB5.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨66, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨80, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨81, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨96, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨97, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨100, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨106, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨108, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨116, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

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
  apply Krenn.X5Case52Tree.LeafB6.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨100, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨102, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨116, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b7`. -/
theorem leafB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.X5Case52Tree.LeafB7.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨102, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨104, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨109, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨111, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨115, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨116, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case52Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

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
        exact leafB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 7)⁻¹ (by simp [zeroD0C2])
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
        exact leafB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 7)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact leafB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 3)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      ·
        exact leafB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 3)⁻¹ (by simp [zeroD0C1]) (values 7)⁻¹ (by simp [zeroD0C2])

theorem selectedHasNoCommonZero (values : Fin 70 → ℂ) :
    ¬ RootSelectedZero values := by
  intro rootZero
  exact rootImpossible values rootZero

#print axioms Krenn.X5Case52Selected.selectedHasNoCommonZero

end Krenn.X5Case52Selected
