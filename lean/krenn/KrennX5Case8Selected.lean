import KrennX5Case8Tree.LeafB0
import KrennX5Case8Tree.LeafB1
import KrennX5Case8Tree.LeafB2
import KrennX5Case8Tree.LeafB3
import KrennX5Case8Tree.LeafB4_0
import KrennX5Case8Tree.LeafB4_1
import KrennX5Case8Tree.LeafB4_2
import KrennX5Case8Tree.LeafB4_3
import KrennX5Case8Tree.LeafB4_4
import KrennX5Case8Tree.LeafB4_5
import KrennX5Case8Tree.LeafB4_6
import KrennX5Case8Tree.LeafB4_7
import KrennX5Case8Tree.LeafB5
import KrennX5Case8Tree.LeafB6_0
import KrennX5Case8Tree.LeafB6_1
import KrennX5Case8Tree.LeafB6_2
import KrennX5Case8Tree.LeafB6_3
import KrennX5Case8Tree.LeafB6_4
import KrennX5Case8Tree.LeafB6_5
import KrennX5Case8Tree.LeafB6_6
import KrennX5Case8Tree.LeafB6_7
import KrennX5Case8Tree.LeafB7

namespace Krenn.X5Case8Selected

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedIndices : Fin 96 → Fin 675 := ![
  0,
  1,
  7,
  8,
  10,
  11,
  12,
  13,
  16,
  17,
  24,
  26,
  27,
  28,
  30,
  34,
  35,
  37,
  38,
  41,
  43,
  46,
  48,
  49,
  50,
  51,
  53,
  54,
  310,
  311,
  312,
  317,
  341,
  391,
  399,
  400,
  402,
  411,
  412,
  414,
  415,
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
  430,
  431,
  432,
  433,
  436,
  438,
  448,
  449,
  452,
  467,
  531,
  534,
  550,
  553,
  570,
  571,
  572,
  573,
  576,
  582,
  583,
  592,
  596,
  619,
  620,
  622,
  627,
  635,
  640,
  642,
  643,
  650,
  658,
  659,
  660,
  661,
  662,
  663,
  664,
  666,
  667,
  671,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedEquations : Fin 96 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (61, 1)] }, { coefficient := 1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (35, 1), (65, 1)] }, { coefficient := 1, powers := [(35, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(36, 1), (66, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (56, 1)] }, { coefficient := 1, powers := [(44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(36, 1), (67, 1)] }, { coefficient := 1, powers := [(39, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (65, 1)] }, { coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (65, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(56, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(17, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

def RootSelectedZero {R : Type*} [CommRing R]
    (values : Fin 70 → R) : Prop :=
  ∀ index : Fin 96,
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
  apply Krenn.X5Case8Tree.LeafB0.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨89, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

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
  apply Krenn.X5Case8Tree.LeafB1.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨89, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0

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
  apply Krenn.X5Case8Tree.LeafB2.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨89, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

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
  apply Krenn.X5Case8Tree.LeafB3.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨89, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0

/-- Frozen compatibility and contradiction for terminal chart `b4.0`. -/
theorem leafB40Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 71 → R := values1
  apply Krenn.X5Case8Tree.LeafB4_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨57, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨70, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨75, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨79, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.1`. -/
theorem leafB41Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case8Tree.LeafB4_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨80, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.2`. -/
theorem leafB42Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case8Tree.LeafB4_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.3`. -/
theorem leafB43Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case8Tree.LeafB4_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.4`. -/
theorem leafB44Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case8Tree.LeafB4_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨72, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨74, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨78, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨88, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.5`. -/
theorem leafB45Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case8Tree.LeafB4_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.6`. -/
theorem leafB46Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case8Tree.LeafB4_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨64, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.7`. -/
theorem leafB47Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
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
    else d0Inverse0
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else if at1 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case8Tree.LeafB4_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

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
  apply Krenn.X5Case8Tree.LeafB5.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨63, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨64, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨66, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨73, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨79, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨80, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨81, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨82, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨83, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨87, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨91, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.0`. -/
theorem leafB60Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 72 → R := values1
  apply Krenn.X5Case8Tree.LeafB6_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨57, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨70, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨75, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨79, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.1`. -/
theorem leafB61Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
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
    else d0Inverse1
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case8Tree.LeafB6_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.2`. -/
theorem leafB62Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
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
    else d0Inverse1
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case8Tree.LeafB6_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.3`. -/
theorem leafB63Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
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
    else d0Inverse1
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case8Tree.LeafB6_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.4`. -/
theorem leafB64Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
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
    else d0Inverse1
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case8Tree.LeafB6_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨72, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨74, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨78, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨88, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.5`. -/
theorem leafB65Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
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
    else d0Inverse1
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case8Tree.LeafB6_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨85, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨90, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.6`. -/
theorem leafB66Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
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
    else d0Inverse1
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case8Tree.LeafB6_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨64, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.7`. -/
theorem leafB67Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
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
    else d0Inverse1
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else if at1 : index.val = 73 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case8Tree.LeafB6_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨86, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case8Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

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
  apply Krenn.X5Case8Tree.LeafB7.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨57, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨58, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨61, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨63, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨64, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨66, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨67, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨79, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨80, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨81, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨82, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨83, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨87, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨92, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨93, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨94, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootSelectedEquations, Krenn.X5Case8Tree.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Exhaustive reflection for carrier chart `b4`. -/
theorem nodeB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB40Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB41Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB42Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB43Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB44Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB45Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB46Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB47Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b6`. -/
theorem nodeB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB60Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB61Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB62Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB63Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB64Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB65Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB66Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB67Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

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
        exact nodeB4Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 zeroD0C2
      ·
        exact leafB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 7)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact nodeB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 3)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      ·
        exact leafB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 3)⁻¹ (by simp [zeroD0C1]) (values 7)⁻¹ (by simp [zeroD0C2])

theorem selectedHasNoCommonZero (values : Fin 70 → ℂ) :
    ¬ RootSelectedZero values := by
  intro rootZero
  exact rootImpossible values rootZero

#print axioms Krenn.X5Case8Selected.selectedHasNoCommonZero

end Krenn.X5Case8Selected
