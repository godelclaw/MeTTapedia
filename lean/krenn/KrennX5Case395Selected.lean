import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case395Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "970da724a788198a060ae0dbbc28e075499d17896e1e81ba38dbe576066e563f"
def sourceSystemSemanticSHA256 : String := "0a0af4f08e31a8f91c0ae8ed8e61a55567a0f3d197030fd871cd7e5c159f7098"
def certificateSHA256 : String := "7fdc0ff3748276abc6b8522fa692083ddafff2fe242a627abbb78a69a7de76a4"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 37 → Fin 675 := ![
  0,
  1,
  2,
  16,
  26,
  27,
  28,
  29,
  42,
  43,
  51,
  224,
  382,
  403,
  414,
  416,
  419,
  421,
  422,
  423,
  424,
  425,
  527,
  533,
  538,
  554,
  577,
  606,
  613,
  638,
  659,
  664,
  665,
  666,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (63, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (38, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (38, 1), (39, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (34, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (16, 1), (18, 1), (26, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (16, 1), (18, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (23, 1), (26, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (32, 1), (38, 1), (68, 1)] }, { coefficient := -1, powers := [(8, 1), (44, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 2), (16, 1), (18, 1), (26, 1), (37, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 2), (16, 1), (18, 1), (35, 1), (50, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 2), (16, 1), (18, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (23, 1), (26, 1), (37, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (23, 1), (35, 1), (50, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (23, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (34, 1), (35, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (38, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (42, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (18, 1), (30, 1), (35, 1), (69, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (30, 1), (35, 1), (69, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (34, 1), (35, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (35, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (33, 1), (35, 1), (36, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (33, 1), (36, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (16, 1), (18, 1), (26, 1), (30, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (18, 1), (30, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (26, 1), (30, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (30, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (24, 1), (26, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (24, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (30, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (16, 1), (24, 1), (35, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (24, 1), (35, 1), (69, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (34, 1), (35, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (16, 1), (24, 1), (35, 1), (69, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (35, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (35, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (35, 1), (36, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (36, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (16, 1), (35, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (35, 1), (69, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (16, 1), (35, 1), (49, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (16, 1), (41, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (32, 1), (41, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (35, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (41, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (41, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(34, 1), (41, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (26, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (26, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (18, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (18, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (16, 1), (18, 1), (35, 1), (69, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (35, 1), (69, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (36, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (16, 1), (26, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (35, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (18, 1), (26, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (18, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (26, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (35, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (26, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case395Selected.selectedHasNoCommonZero

end Krenn.X5Case395Selected
