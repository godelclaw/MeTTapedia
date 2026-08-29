import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase817.LeafB0

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "fe081ba7bb93a25862f7b17a5cffb5b362efa225108b3f38a0c33365ddba3ae3"
def sourceSystemSemanticSHA256 : String := "b9f18f4692c31c59e31680e88535ce933fb4c05200a3400405451d32daa39a49"
def certificateSHA256 : String := "c84ac1ec8cdde64c601fd50e62b6a31af45c4e61fc2bb05aa8302a9933501766"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 36 → Fin 678 := ![
  2,
  5,
  24,
  29,
  33,
  47,
  48,
  49,
  388,
  420,
  422,
  423,
  424,
  425,
  426,
  427,
  439,
  544,
  576,
  606,
  627,
  639,
  650,
  656,
  661,
  664,
  666,
  668,
  669,
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
def selectedEquations : Fin 36 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (61, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(1, 1), (3, 1), (6, 1), (47, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (47, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (47, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (47, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (15, 1), (25, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (15, 1), (33, 1), (41, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (25, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (33, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (25, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (33, 1), (41, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (33, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (9, 1), (15, 1), (21, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (9, 1), (21, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (15, 1), (21, 1), (33, 1), (41, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (21, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (33, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (15, 1), (21, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (21, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (21, 1), (33, 1), (41, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (9, 1), (15, 1), (28, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (9, 1), (28, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (15, 1), (28, 1), (33, 1), (41, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (28, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (29, 1)] }, { coefficient := -1, powers := [(1, 1), (31, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (15, 1), (29, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (26, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (15, 1), (28, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (28, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (28, 1), (33, 1), (41, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (33, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (15, 1), (18, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (18, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (18, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (21, 1)] }, { coefficient := -1, powers := [(1, 1), (23, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (15, 1), (21, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (3, 1), (6, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (33, 1), (41, 1), (48, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (41, 1), (48, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(33, 1), (40, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (3, 1), (6, 1), (15, 1), (25, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (6, 1), (25, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (6, 1), (25, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (6, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (15, 1), (28, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (28, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (28, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (15, 1), (25, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (25, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (28, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (3, 1), (6, 1), (15, 1), (17, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (6, 1), (17, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (6, 1), (17, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (6, 1), (17, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (15, 1), (20, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (20, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (20, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (20, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (15, 1), (17, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (17, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (20, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (10, 1), (15, 1), (29, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (26, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (10, 1), (15, 1), (21, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (8, 1), (23, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (13, 1), (23, 1), (24, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (23, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (24, 1), (41, 1), (60, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (3, 1), (6, 1), (9, 1), (15, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (6, 1), (9, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (6, 1), (9, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (6, 1), (9, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (12, 1), (15, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (12, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (12, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (12, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (15, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (15, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (9, 1), (15, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (9, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (15, 1), (33, 1), (41, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (15, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (33, 1), (41, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (23, 1), (35, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (23, 1), (41, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (35, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (41, 1), (58, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (23, 1), (24, 1), (35, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (23, 1), (24, 1), (41, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (24, 1), (35, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (24, 1), (41, 1), (58, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (15, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (33, 1), (39, 1), (41, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (15, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (33, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (10, 1), (15, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (23, 1), (24, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (41, 1), (60, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (3, 1), (6, 1), (15, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (6, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (6, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (6, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (15, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (23, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (41, 1), (60, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (15, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (41, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (6, 1), (23, 1), (41, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (41, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (6, 1), (23, 1), (24, 1), (41, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (23, 1), (32, 1), (41, 2), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (24, 1), (41, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (32, 1), (41, 2), (60, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (6, 1), (23, 1), (41, 1), (60, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (41, 1), (60, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (6, 1), (23, 1), (24, 1), (41, 1), (60, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (16, 1), (23, 1), (41, 1), (44, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (23, 1), (24, 1), (41, 1), (44, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (23, 1), (32, 1), (38, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (24, 1), (41, 1), (60, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (41, 1), (44, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (24, 1), (41, 1), (44, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (32, 1), (38, 1), (41, 1), (60, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (6, 1), (23, 1), (35, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (35, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (6, 1), (23, 1), (24, 1), (35, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (10, 1), (23, 1), (35, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(1, 1), (6, 1), (10, 1), (23, 1), (41, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (15, 1), (23, 1), (24, 1), (35, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (15, 1), (23, 1), (24, 1), (41, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (23, 1), (32, 1), (35, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (23, 1), (24, 1), (35, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (23, 1), (35, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (23, 1), (41, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (23, 1), (24, 1), (35, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (23, 1), (24, 1), (41, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (32, 1), (35, 1), (41, 1), (60, 1), (69, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase817.LeafB0.selectedHasNoCommonZero

end Krenn.X5ResidualCase817.LeafB0
