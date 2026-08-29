import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase388.LeafB0

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "0961c0ce4e981120d755941966f83f60cbaf0a06749b65444e2249432873c258"
def sourceSystemSemanticSHA256 : String := "1ae1dcf1ff826157a59099b2977eb1c2cfddbf04dd6e099871b7d884f27aa7a3"
def certificateSHA256 : String := "b3eb4cb635b72e2ea14553db49e13b221f199dd16c8b8572fa7723bc693dd634"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 41 → Fin 678 := ![
  4,
  24,
  26,
  27,
  29,
  30,
  33,
  34,
  43,
  47,
  48,
  49,
  55,
  56,
  382,
  384,
  406,
  411,
  418,
  421,
  422,
  423,
  424,
  425,
  426,
  434,
  517,
  534,
  538,
  612,
  626,
  633,
  664,
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
def selectedEquations : Fin 41 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(12, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(36, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 41 → SparsePoly (Fin 70) := ![
  [{ coefficient := -2, powers := [(7, 1), (15, 1), (16, 1), (32, 1), (35, 1), (36, 1), (40, 1), (50, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (24, 1), (32, 1), (35, 1), (36, 1), (40, 1), (50, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (32, 1), (36, 1), (40, 1), (50, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (50, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (36, 1), (40, 1), (50, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (36, 1), (50, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (25, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (43, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (15, 1), (16, 1), (28, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (24, 1), (28, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (28, 1), (32, 1), (36, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (32, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (32, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (32, 1), (36, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (32, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (15, 1), (16, 1), (20, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (20, 1), (24, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (20, 1), (32, 1), (36, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (32, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (32, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (32, 1), (36, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (32, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(15, 1), (26, 1), (33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 2), (33, 1), (54, 1), (56, 1), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (16, 1), (33, 1), (35, 1), (40, 1), (56, 1), (64, 1), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (15, 1), (24, 1), (33, 1), (35, 1), (40, 1), (56, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (33, 1), (37, 1), (56, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (18, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (18, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (15, 1), (16, 1), (33, 1), (35, 1), (40, 1), (53, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (15, 1), (24, 1), (33, 1), (35, 1), (40, 1), (53, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (33, 1), (40, 1), (53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (25, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (25, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (33, 1), (39, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (17, 1), (33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (40, 1), (42, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (40, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (53, 1), (69, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (15, 1), (16, 1), (33, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (24, 1), (33, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (33, 1), (36, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(33, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (7, 1), (15, 1), (16, 1), (25, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(3, 1), (7, 1), (15, 1), (24, 1), (25, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (15, 1), (25, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (15, 1), (25, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (16, 1), (28, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (15, 1), (24, 1), (28, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (28, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (28, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (7, 1), (15, 1), (16, 1), (17, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(3, 1), (7, 1), (15, 1), (17, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (15, 1), (17, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (15, 1), (17, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (16, 1), (20, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (15, 1), (20, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (20, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (20, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (15, 1), (16, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (15, 1), (24, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (16, 1), (40, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (24, 1), (40, 1), (58, 1), (69, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (7, 1), (9, 1), (15, 1), (16, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(3, 1), (7, 1), (9, 1), (15, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (11, 1), (15, 1), (16, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (11, 1), (15, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (69, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (15, 1), (16, 1), (33, 1), (35, 1), (40, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (15, 1), (24, 1), (33, 1), (35, 1), (40, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (33, 1), (40, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (15, 1), (16, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (15, 1), (24, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (15, 1), (32, 1), (36, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (36, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (15, 1), (16, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (24, 1), (40, 1), (64, 1), (69, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (7, 1), (15, 1), (16, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(3, 1), (7, 1), (15, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (15, 1), (16, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (15, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (15, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (15, 1), (16, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (15, 1), (24, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (16, 1), (40, 1), (44, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (24, 1), (40, 1), (44, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (32, 1), (40, 1), (41, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (32, 1), (40, 1), (41, 1), (67, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (40, 1), (64, 2), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (15, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (15, 1), (16, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (15, 1), (24, 1), (40, 1), (64, 2), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (16, 1), (40, 1), (44, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (24, 1), (40, 1), (44, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (32, 1), (38, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (32, 1), (38, 1), (40, 1), (67, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (40, 1), (58, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (15, 1), (40, 1), (58, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (15, 1), (16, 1), (40, 1), (58, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (15, 1), (24, 1), (40, 1), (58, 1), (64, 1), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (14, 1), (15, 1), (16, 1), (33, 1), (35, 1), (40, 1), (47, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (14, 1), (15, 1), (24, 1), (33, 1), (35, 1), (40, 1), (47, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (15, 1), (33, 1), (40, 1), (47, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (16, 1), (40, 1), (44, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (24, 1), (40, 1), (44, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (32, 1), (35, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (32, 1), (35, 1), (40, 1), (67, 1), (69, 1)] }]
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
    ¬ ∀ index : Fin 41,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase388.LeafB0.selectedHasNoCommonZero

end Krenn.X5ResidualCase388.LeafB0
