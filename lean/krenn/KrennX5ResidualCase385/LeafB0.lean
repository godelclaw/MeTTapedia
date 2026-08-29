import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase385.LeafB0

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "7b4830ca7c1af4863546f27ef145c412b34566ba3100e03ecd1c3307d02e0813"
def sourceSystemSemanticSHA256 : String := "6cafcda7369ad5379c1b61f7c87f62c41ac4f9bd162e7e363f8ac077a465301b"
def certificateSHA256 : String := "aa176930507b1a060b73f9819a22bc2be16c5050d485b969c821a6221e271a27"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 37 → Fin 678 := ![
  2,
  5,
  19,
  24,
  25,
  29,
  32,
  33,
  47,
  48,
  313,
  389,
  412,
  413,
  420,
  422,
  423,
  424,
  425,
  426,
  427,
  439,
  538,
  576,
  606,
  627,
  632,
  638,
  663,
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
def selectedEquations : Fin 37 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (61, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (47, 1), (60, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (15, 1), (47, 1), (51, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (47, 1), (60, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (47, 1), (51, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (42, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (15, 1), (25, 1), (33, 1), (39, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (33, 1), (41, 1), (60, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (25, 1), (33, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (33, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (25, 1), (33, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (33, 1), (43, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (33, 1), (40, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (33, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (33, 1), (40, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (33, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (9, 1), (15, 1), (18, 1), (33, 1), (39, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (9, 1), (18, 1), (33, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (15, 1), (18, 1), (33, 1), (41, 1), (53, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (33, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (33, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (15, 1), (18, 1), (33, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (18, 1), (33, 1), (43, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (33, 1), (40, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (33, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (9, 1), (15, 1), (25, 1), (33, 1), (39, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (9, 1), (25, 1), (33, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (15, 1), (25, 1), (33, 1), (41, 1), (53, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (25, 1), (33, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (15, 1), (25, 1), (33, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (25, 1), (33, 1), (43, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (15, 1), (18, 1), (33, 1), (39, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (33, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (18, 1), (33, 1), (39, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (60, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (51, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (33, 1), (41, 1), (48, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (48, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (40, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (43, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (33, 1), (41, 1), (42, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 2), (38, 1), (39, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (15, 1), (25, 1), (41, 1), (60, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (25, 1), (34, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (25, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (25, 1), (60, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (25, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (25, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (25, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (25, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (25, 1), (34, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (25, 1), (34, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (28, 1), (41, 1), (60, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (28, 1), (34, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (28, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (28, 1), (60, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (28, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (28, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (28, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (34, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (34, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (25, 1), (34, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (34, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (34, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (33, 1), (34, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (15, 1), (17, 1), (41, 1), (60, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (17, 1), (34, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (17, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (17, 1), (60, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (17, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (17, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (17, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (34, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (34, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (20, 1), (41, 1), (60, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (20, 1), (34, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (20, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (20, 1), (60, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (20, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (20, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (20, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (34, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (34, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (20, 1), (34, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (33, 1), (34, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1)] }, { coefficient := 1, powers := [(20, 2), (34, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (33, 1), (34, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (31, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (23, 1), (41, 1), (60, 2), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (13, 1), (23, 1), (24, 1), (41, 1), (60, 2), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (9, 1), (15, 1), (41, 1), (60, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (9, 1), (34, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (9, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (9, 1), (60, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (15, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (15, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (15, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (34, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (34, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (11, 1), (15, 1), (41, 1), (60, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (11, 1), (34, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (11, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (11, 1), (60, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (15, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (15, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (15, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (34, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (34, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (20, 1), (34, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (33, 1), (34, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (34, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (34, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (60, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (51, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (9, 1), (15, 1), (33, 1), (39, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (9, 1), (33, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (33, 1), (41, 1), (53, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (33, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (15, 1), (33, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (33, 1), (43, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (35, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (41, 1), (58, 1), (60, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (24, 1), (35, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (24, 1), (41, 1), (58, 1), (60, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (33, 1), (39, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (33, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (33, 1), (39, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (60, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (33, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 2), (38, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (24, 1), (41, 1), (60, 2), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (15, 1), (41, 1), (60, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (34, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (60, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (15, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (15, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (15, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (34, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (34, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (34, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (34, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (41, 1), (60, 2), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (15, 1), (41, 1), (60, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (60, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (7, 1), (23, 1), (41, 1), (60, 2), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (24, 1), (41, 1), (60, 2), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (32, 1), (41, 2), (60, 2), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (7, 1), (23, 1), (41, 1), (60, 2), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (24, 1), (41, 1), (60, 2), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (16, 1), (23, 1), (41, 1), (44, 1), (60, 2), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (24, 1), (41, 1), (44, 1), (60, 2), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (32, 1), (38, 1), (41, 1), (60, 2), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (7, 1), (23, 1), (35, 1), (60, 2), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (24, 1), (35, 1), (60, 2), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (23, 1), (24, 1), (35, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (23, 1), (24, 1), (41, 1), (58, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (32, 1), (35, 1), (41, 1), (60, 2), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (35, 1), (60, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (41, 1), (58, 1), (60, 1), (69, 1)] }]
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

#print axioms Krenn.X5ResidualCase385.LeafB0.selectedHasNoCommonZero

end Krenn.X5ResidualCase385.LeafB0
