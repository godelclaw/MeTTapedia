import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case319Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "b0fbd3b92df54ae68a7cf591189b5a3753c7211cab8457f80fdd52f054b24f0c"
def sourceSystemSemanticSHA256 : String := "bf7a34439b145b832d1b53274ad8605dc24386b78dabb02106512fc4c1327f1e"
def certificateSHA256 : String := "acc53d8730336952fdc42a5aef5cf9941ab448639a994e62f91b31244392582d"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 42 → Fin 675 := ![
  0,
  1,
  2,
  8,
  27,
  28,
  29,
  33,
  43,
  84,
  315,
  369,
  414,
  416,
  417,
  419,
  420,
  422,
  423,
  424,
  425,
  426,
  427,
  445,
  476,
  485,
  524,
  542,
  578,
  583,
  612,
  614,
  622,
  643,
  659,
  661,
  666,
  667,
  670,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (38, 1), (69, 1)] }, { coefficient := 1, powers := [(29, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(47, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(35, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(27, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (11, 1), (15, 1), (16, 1), (43, 1), (48, 1), (62, 1), (66, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (11, 1), (15, 1), (32, 1), (43, 1), (48, 1), (61, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (11, 1), (15, 1), (16, 1), (43, 1), (62, 1), (66, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (11, 1), (15, 1), (32, 1), (43, 1), (61, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (32, 1), (39, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (15, 1), (16, 1), (28, 1), (43, 1), (45, 1), (48, 1), (62, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (15, 1), (24, 1), (43, 1), (44, 1), (48, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (15, 1), (26, 1), (41, 1), (48, 1), (49, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (15, 1), (28, 1), (32, 1), (43, 1), (45, 1), (48, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (15, 1), (16, 1), (28, 1), (43, 1), (45, 1), (62, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (15, 1), (24, 1), (43, 1), (44, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (15, 1), (26, 1), (41, 1), (49, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (15, 1), (28, 1), (32, 1), (43, 1), (45, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (32, 1), (39, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (39, 1), (41, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (11, 1), (34, 1), (48, 1), (57, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (11, 1), (34, 1), (57, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (26, 1), (28, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (28, 1), (47, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (25, 1), (34, 1), (48, 1), (50, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (43, 1), (48, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (48, 1), (50, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (25, 1), (34, 1), (50, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (34, 1), (43, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (50, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (39, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (28, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (47, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (39, 1), (43, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (28, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (28, 1), (34, 1), (37, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (43, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (22, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (22, 1), (28, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (28, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (33, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (28, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (39, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (39, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (18, 1), (34, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (23, 1), (48, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (18, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (23, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (11, 1), (29, 1), (48, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (11, 1), (29, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (29, 1), (39, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (34, 1), (39, 1), (40, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (11, 1), (12, 1), (48, 1), (62, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (15, 1), (43, 1), (48, 1), (62, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (11, 1), (15, 1), (16, 1), (43, 1), (48, 1), (62, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (11, 1), (15, 1), (32, 1), (43, 1), (48, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (15, 1), (32, 1), (43, 1), (48, 1), (55, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (11, 1), (12, 1), (62, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (15, 1), (43, 1), (62, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (11, 1), (15, 1), (16, 1), (43, 1), (62, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (11, 1), (15, 1), (32, 1), (43, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (15, 1), (32, 1), (43, 1), (55, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (11, 1), (32, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (22, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (18, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (28, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (28, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (40, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (39, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (39, 1), (40, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (48, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (28, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (47, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (48, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (11, 1), (15, 1), (43, 1), (46, 1), (48, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (11, 1), (15, 1), (43, 1), (46, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (39, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (16, 1), (39, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (33, 1), (36, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (15, 1), (43, 1), (44, 1), (48, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (15, 1), (43, 1), (44, 1), (62, 1), (66, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (45, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (28, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (68, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (15, 1), (24, 1), (43, 1), (48, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (15, 1), (24, 1), (43, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (27, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (31, 1), (48, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (31, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (28, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (48, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (23, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (28, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (11, 1), (16, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (48, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (39, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (11, 1), (48, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (11, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (39, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (39, 1), (40, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (34, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (15, 1), (16, 1), (43, 1), (48, 1), (62, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (15, 1), (32, 1), (43, 1), (48, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (15, 1), (16, 1), (43, 1), (62, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (15, 1), (32, 1), (43, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (11, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (48, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (15, 1), (41, 1), (48, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (15, 1), (41, 1), (62, 1), (66, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (11, 1), (15, 1), (43, 1), (48, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (11, 1), (15, 1), (43, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (16, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (28, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (16, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (15, 1), (43, 1), (48, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (15, 1), (43, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (48, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case319Selected.selectedHasNoCommonZero

end Krenn.X5Case319Selected
