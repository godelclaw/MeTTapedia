import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case52Tree.LeafB1

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "760060406f5b1fc7494583978e5d993c101f372b7897c916fbd7b72e67564fe3"
def sourceSystemSemanticSHA256 : String := "a15ef2a985557d6eb1f241af9907531be7aa4ff28e13360b32a8d4b7ac0c7cf2"
def certificateSHA256 : String := "4c2b7fd837a64a7ca976f68d7d13be0d51750a330ef48d46541628b7a7b3f33a"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 36 → Fin 678 := ![
  0,
  1,
  20,
  23,
  31,
  43,
  47,
  48,
  53,
  320,
  349,
  350,
  417,
  419,
  421,
  422,
  423,
  424,
  425,
  426,
  440,
  649,
  651,
  658,
  659,
  660,
  661,
  666,
  667,
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
def selectedEquations : Fin 36 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (24, 2), (33, 1), (36, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (24, 2), (33, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (24, 1), (33, 1), (36, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (24, 1), (33, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (24, 2), (33, 1), (36, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (24, 2), (33, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (24, 1), (32, 1), (36, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (24, 1), (32, 1), (39, 1), (45, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (32, 1), (36, 1), (45, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (32, 1), (39, 1), (45, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (24, 1), (32, 1), (36, 1), (45, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (24, 1), (32, 1), (39, 1), (45, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (9, 1), (23, 1), (33, 1), (42, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (42, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (42, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (37, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (33, 1), (42, 1), (51, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (51, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (34, 1), (42, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (24, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (24, 2), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (24, 2), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (32, 1), (39, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (39, 1), (45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (33, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (26, 1), (33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (26, 1), (33, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (33, 1), (42, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (40, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1), (33, 1), (42, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (50, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (42, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1), (33, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 2), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 2), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (39, 1), (45, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(32, 1), (39, 1), (45, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (39, 1), (45, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1), (33, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1), (52, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (55, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 2), (33, 1), (36, 1), (52, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 2), (33, 1), (36, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 2), (33, 1), (39, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 2), (33, 1), (39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (36, 1), (45, 1), (52, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (36, 1), (45, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (39, 1), (45, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (39, 1), (45, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (59, 1), (62, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case52Tree.LeafB1.selectedHasNoCommonZero

end Krenn.X5Case52Tree.LeafB1
