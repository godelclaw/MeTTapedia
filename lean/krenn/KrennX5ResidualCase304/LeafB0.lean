import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase304.LeafB0

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "2be83d64191414a3811f3fc30153c528d80b4b7a32ed225e83dc1614cd046e20"
def sourceSystemSemanticSHA256 : String := "cc7b8faa8f7939793501e2292a35016436715456519c7407eb976a59dd090c91"
def certificateSHA256 : String := "9f3cfaf54e672e6cdaaebeeb05c94e9256b9bf2b0d6536933eea2208ef26941a"
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
  347,
  351,
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
  482,
  534,
  538,
  594,
  626,
  633,
  664,
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
  [{ coefficient := 1, powers := [(4, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(36, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 41 → SparsePoly (Fin 70) := ![
  [{ coefficient := -2, powers := [(4, 1), (15, 1), (16, 1), (32, 1), (35, 1), (36, 1), (40, 1), (50, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (24, 1), (32, 1), (35, 1), (36, 1), (40, 1), (50, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (32, 1), (36, 1), (40, 1), (50, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (50, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (36, 1), (40, 1), (50, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (36, 1), (50, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (25, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (43, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (15, 1), (16, 1), (27, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (24, 1), (27, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (27, 1), (32, 1), (36, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (32, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (32, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (32, 1), (36, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (32, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (15, 1), (16, 1), (19, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (19, 1), (24, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (19, 1), (32, 1), (36, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (32, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (32, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (32, 1), (36, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (32, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(15, 1), (26, 1), (33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (7, 1), (33, 1), (54, 1), (56, 1), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (16, 1), (33, 1), (35, 1), (40, 1), (56, 1), (64, 1), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (15, 1), (24, 1), (33, 1), (35, 1), (40, 1), (56, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (33, 1), (40, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (33, 1), (40, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (33, 1), (37, 1), (56, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (18, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (18, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (15, 1), (16, 1), (33, 1), (35, 1), (40, 1), (53, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (15, 1), (24, 1), (33, 1), (35, 1), (40, 1), (53, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (33, 1), (40, 1), (53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (25, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (25, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (33, 1), (39, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (17, 1), (33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (40, 1), (42, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (40, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (53, 1), (69, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (15, 1), (16, 1), (33, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (24, 1), (33, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (33, 1), (36, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(33, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (4, 1), (15, 1), (16, 1), (25, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(3, 1), (4, 1), (15, 1), (24, 1), (25, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (15, 1), (25, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (15, 1), (25, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (16, 1), (27, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (15, 1), (24, 1), (27, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (27, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (27, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (4, 1), (15, 1), (16, 1), (17, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(3, 1), (4, 1), (15, 1), (17, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (15, 1), (17, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (15, 1), (17, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (16, 1), (19, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (15, 1), (19, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (19, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (19, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (15, 1), (16, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (15, 1), (24, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (16, 1), (40, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (24, 1), (40, 1), (58, 1), (69, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (4, 1), (9, 1), (15, 1), (16, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(3, 1), (4, 1), (9, 1), (15, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (9, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (9, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (11, 1), (15, 1), (16, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (11, 1), (15, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (11, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (11, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (69, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (15, 1), (16, 1), (33, 1), (35, 1), (40, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (15, 1), (24, 1), (33, 1), (35, 1), (40, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (33, 1), (40, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (15, 1), (16, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (15, 1), (24, 1), (32, 1), (35, 1), (36, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (15, 1), (32, 1), (36, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (36, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (36, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1), (16, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (24, 1), (40, 1), (64, 1), (69, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (4, 1), (15, 1), (16, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -2, powers := [(3, 1), (4, 1), (15, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (15, 1), (16, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (15, 1), (24, 1), (35, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (15, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (15, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (15, 1), (16, 1), (40, 1), (67, 2), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (15, 1), (24, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (16, 1), (40, 1), (44, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (24, 1), (40, 1), (44, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (32, 1), (40, 1), (41, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (32, 1), (40, 1), (41, 1), (67, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (15, 1), (40, 1), (64, 2), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (15, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (15, 1), (16, 1), (40, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (15, 1), (24, 1), (40, 1), (64, 2), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (16, 1), (40, 1), (44, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (24, 1), (40, 1), (44, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (32, 1), (38, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (32, 1), (38, 1), (40, 1), (67, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (15, 1), (40, 1), (58, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (15, 1), (40, 1), (58, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (15, 1), (16, 1), (40, 1), (58, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (15, 1), (24, 1), (40, 1), (58, 1), (64, 1), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (11, 1), (15, 1), (16, 1), (33, 1), (35, 1), (40, 1), (47, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := 2, powers := [(4, 1), (11, 1), (15, 1), (24, 1), (33, 1), (35, 1), (40, 1), (47, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (11, 1), (15, 1), (33, 1), (40, 1), (47, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (16, 1), (40, 1), (44, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (24, 1), (40, 1), (44, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (32, 1), (35, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (32, 1), (35, 1), (40, 1), (67, 1), (69, 1)] }]
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

#print axioms Krenn.X5ResidualCase304.LeafB0.selectedHasNoCommonZero

end Krenn.X5ResidualCase304.LeafB0
