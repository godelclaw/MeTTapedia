import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase170.LeafB0

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "455c21c2789d300fe167bf272a98a1f52e78fcc04c2b8d2d04898c3131edf0ef"
def sourceSystemSemanticSHA256 : String := "5f238f467c26f52f636c5866add44992e31636516121e26a4a59557a792a58e2"
def certificateSHA256 : String := "a8d558d2c6debe0ffcb335e761d044ab26df62c637d809844a55f0f4c48978cc"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 31 → Fin 678 := ![
  5,
  24,
  25,
  26,
  27,
  30,
  34,
  41,
  42,
  44,
  46,
  50,
  52,
  398,
  405,
  411,
  417,
  421,
  422,
  423,
  424,
  426,
  534,
  542,
  543,
  633,
  660,
  663,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(14, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (37, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (37, 1), (48, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (26, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (26, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (26, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (32, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (11, 1), (26, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (11, 1), (26, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (11, 1), (26, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (26, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (26, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (26, 1), (33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (32, 1), (37, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (18, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (18, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (18, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (11, 1), (18, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (11, 1), (18, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (11, 1), (18, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (18, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (18, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (18, 1), (33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (32, 1), (37, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (34, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (26, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (26, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (26, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (18, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (18, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (18, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (34, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (34, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (36, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(34, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(34, 1), (42, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (11, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (11, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (11, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase170.LeafB0.selectedHasNoCommonZero

end Krenn.X5ResidualCase170.LeafB0
