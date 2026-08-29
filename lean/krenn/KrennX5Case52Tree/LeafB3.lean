import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case52Tree.LeafB3

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "a223a47c47562502d70557eb9d1b842f8b7bde8c9334049be1c5231fb4ced32b"
def sourceSystemSemanticSHA256 : String := "34c8b544b0c5552441bfd4accb6fa34fe1ed65b495b0361be3e96f2432abf016"
def certificateSHA256 : String := "7a775443f9ac6ee326075e5e8561d86d351bde52e3c7c572432d4ecb1af406c5"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 54 → Fin 678 := ![
  0,
  1,
  9,
  11,
  20,
  23,
  28,
  30,
  31,
  33,
  38,
  43,
  50,
  53,
  310,
  343,
  349,
  350,
  398,
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
  436,
  440,
  447,
  469,
  500,
  535,
  568,
  581,
  582,
  617,
  629,
  650,
  651,
  658,
  659,
  661,
  664,
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
def selectedEquations : Fin 54 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
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
  [{ coefficient := 1, powers := [(3, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (59, 1)] }, { coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 54 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (33, 1), (36, 1), (40, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (33, 1), (39, 1), (40, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (37, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (3, 1), (17, 1), (34, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (23, 1), (60, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (34, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (11, 1), (17, 1), (34, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (11, 1), (17, 1), (34, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (11, 1), (34, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (34, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (23, 1), (32, 1), (37, 1), (38, 1), (58, 1), (66, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (29, 1), (32, 1), (37, 1), (38, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (34, 1), (50, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (50, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (37, 1), (38, 1), (58, 1), (66, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (32, 1), (37, 1), (38, 1), (66, 1), (70, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (32, 1), (37, 1), (38, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (42, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (50, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (50, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (37, 1), (38, 1), (66, 1), (70, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (42, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(29, 1), (32, 1), (37, 1), (38, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (48, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (51, 1), (54, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (51, 1), (54, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (51, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(34, 1), (42, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (32, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (26, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (34, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (26, 1), (34, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (26, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (34, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (34, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (26, 1), (32, 1), (37, 1), (38, 1), (66, 1), (70, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (32, 1), (37, 1), (38, 1), (66, 1), (70, 1)] }, { coefficient := -1, powers := [(13, 1), (26, 1), (32, 1), (37, 1), (38, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (37, 1), (38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (32, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (31, 1), (32, 1), (36, 1), (40, 1), (47, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (31, 1), (32, 1), (39, 1), (40, 1), (47, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (31, 1), (32, 1), (36, 1), (40, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (31, 1), (32, 1), (39, 1), (40, 1), (45, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (34, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (25, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (23, 1), (26, 1), (32, 1), (37, 1), (38, 1), (70, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (32, 1), (37, 1), (38, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1), (32, 1), (37, 1), (38, 1), (70, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (37, 1), (38, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (54, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (54, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (54, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (54, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (54, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (49, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (49, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (40, 1), (50, 1), (60, 1), (71, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (50, 1), (57, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (40, 1), (50, 1), (60, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (50, 1), (57, 1), (71, 1)] }, { coefficient := -1, powers := [(33, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (31, 1), (33, 1), (36, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (33, 1), (39, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1), (25, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (33, 1), (36, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (33, 1), (39, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(29, 1), (32, 1), (37, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (32, 1), (36, 1), (40, 1), (47, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (32, 1), (39, 1), (40, 1), (47, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1), (32, 1), (37, 1), (38, 1), (66, 1), (70, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (37, 1), (38, 1), (66, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (32, 1), (37, 1), (38, 1), (66, 1)] }, { coefficient := -1, powers := [(32, 1), (37, 1), (38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (39, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (32, 1), (37, 1), (38, 1), (66, 1), (70, 1)] }, { coefficient := -1, powers := [(29, 1), (32, 1), (37, 1), (38, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (37, 1), (38, 1), (66, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (32, 1), (36, 1), (40, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (39, 1), (40, 1), (45, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (40, 1), (60, 1), (71, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (71, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (40, 1), (60, 1), (71, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (32, 1), (36, 1), (40, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (32, 1), (39, 1), (40, 1), (45, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (32, 1), (36, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (39, 1), (40, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (33, 1), (36, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (39, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (40, 1), (52, 1), (60, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (40, 1), (55, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (40, 1), (52, 1), (56, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (40, 1), (55, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (52, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (55, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (23, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (32, 1), (37, 1), (38, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (37, 1), (38, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (40, 1), (53, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (40, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (40, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (40, 1), (53, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (40, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (40, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (59, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 54,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case52Tree.LeafB3.selectedHasNoCommonZero

end Krenn.X5Case52Tree.LeafB3
