import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case61Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "fbb689e62dcfd951590e0b26c4cd633b83f7da72b07c1a1852891b5dd491d8e3"
def sourceSystemSemanticSHA256 : String := "fd47822209fc0da15c5b4a6c1184b709be35e8ed42dbfd4eabcba178344c5b25"
def certificateSHA256 : String := "bf5ca385c191993e53777e68fc652780832cfa79fad80b99a66d4d7a4788744d"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 47 → Fin 675 := ![
  0,
  1,
  10,
  13,
  16,
  17,
  19,
  24,
  25,
  29,
  32,
  33,
  38,
  40,
  44,
  45,
  51,
  397,
  398,
  404,
  408,
  413,
  414,
  416,
  421,
  422,
  423,
  424,
  425,
  426,
  436,
  464,
  531,
  534,
  559,
  605,
  629,
  635,
  640,
  659,
  662,
  663,
  669,
  671,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(36, 1), (69, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }, { coefficient := 1, powers := [(53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (25, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (32, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (24, 1), (25, 1), (45, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (32, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (32, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (24, 1), (25, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (25, 1), (32, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (14, 1), (24, 1), (25, 1), (45, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (14, 1), (25, 1), (32, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (14, 1), (32, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (34, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (33, 1), (37, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (47, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (47, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (47, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (47, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (45, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (34, 1), (37, 1), (45, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (45, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (42, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (41, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (41, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (34, 1), (37, 1), (45, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (26, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (33, 1), (41, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (43, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (24, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (25, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (23, 1), (34, 1), (37, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (24, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (25, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (34, 1), (37, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (15, 1), (33, 1), (39, 1), (56, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (34, 1), (39, 1), (56, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (32, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (26, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (39, 1), (56, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (33, 1), (37, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (46, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (46, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (46, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (24, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (24, 1), (46, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (36, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (34, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (34, 1), (37, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(34, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case61Selected.selectedHasNoCommonZero

end Krenn.X5Case61Selected
