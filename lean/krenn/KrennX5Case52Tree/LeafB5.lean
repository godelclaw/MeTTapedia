import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case52Tree.LeafB5

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "e19ba8f9e65fac5915803681e702581ef3894de0f709cf22d47f8e613a7b2894"
def sourceSystemSemanticSHA256 : String := "e3199ab15df6f0be8432e43dbed033d231e0ae987884dbe881fdd0c2b22ab389"
def certificateSHA256 : String := "0448bcf469f5f952f327a304e43d9528aeaec8bdffbf215cb631a2b9ca0cb116"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 39 → Fin 678 := ![
  1,
  9,
  11,
  20,
  25,
  26,
  30,
  40,
  47,
  48,
  50,
  307,
  311,
  349,
  416,
  417,
  419,
  420,
  422,
  423,
  424,
  426,
  436,
  535,
  559,
  582,
  629,
  640,
  642,
  643,
  660,
  662,
  664,
  666,
  671,
  673,
  674,
  675,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(36, 1), (69, 1)] }, { coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (59, 1)] }, { coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }, { coefficient := 1, powers := [(53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 72) := ![
  [{ coefficient := -1, powers := [(1, 1), (7, 1), (11, 1), (17, 1), (32, 1), (42, 1), (54, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (7, 1), (19, 1), (32, 1), (42, 1), (54, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (23, 1), (49, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (17, 1), (32, 1), (42, 1), (50, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (33, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (32, 1), (42, 1), (50, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (48, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (42, 1), (50, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (33, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (7, 1), (25, 1), (33, 1), (53, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (11, 1), (17, 1), (26, 1), (32, 1), (42, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (26, 1), (32, 1), (42, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (42, 1), (54, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (33, 1), (54, 1), (56, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (26, 1)] }, { coefficient := -1, powers := [(1, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (11, 1), (26, 1), (32, 1), (42, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (54, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (54, 1), (56, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (25, 1), (33, 1), (36, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (42, 1), (50, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (11, 1), (45, 1), (54, 1), (69, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (45, 1), (57, 1), (66, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (45, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (45, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (11, 1), (25, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (25, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (11, 1), (17, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (17, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (11, 1), (32, 1), (42, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (17, 1), (33, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (11, 1), (17, 1), (32, 1), (42, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (32, 1), (42, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (42, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (11, 1), (54, 1), (69, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (57, 1), (66, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (42, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (11, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (11, 1), (53, 1), (54, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (53, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (54, 1), (56, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (54, 1), (59, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (56, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (53, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (53, 1), (54, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (53, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (54, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (53, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (54, 1), (56, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (54, 1), (59, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (53, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1), (59, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case52Tree.LeafB5.selectedHasNoCommonZero

end Krenn.X5Case52Tree.LeafB5
