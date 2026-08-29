import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case574Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "5bfc5af0348fff97ef4d08c9a8c6eb054ff3e2c4b93935d3a42ed53074e7ea3c"
def sourceSystemSemanticSHA256 : String := "1cc391fe7a6881a4a9e23fc7a2870434db3bc0aabbaf99653b0fd56631ad0e01"
def certificateSHA256 : String := "80975a33b6ef86524beccfcc7519ed0873ebcd0b12d92d787803f38ea121c568"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 45 → Fin 675 := ![
  0,
  1,
  2,
  3,
  5,
  25,
  26,
  30,
  31,
  33,
  38,
  46,
  49,
  353,
  385,
  389,
  415,
  417,
  418,
  420,
  421,
  422,
  423,
  424,
  425,
  431,
  437,
  536,
  539,
  560,
  583,
  596,
  609,
  611,
  614,
  628,
  639,
  652,
  661,
  665,
  667,
  670,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (11, 1), (62, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (11, 1), (47, 1), (62, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (28, 1), (33, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (28, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (48, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (8, 1), (11, 1), (62, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (11, 1), (32, 1), (55, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (8, 1), (11, 1), (47, 1), (62, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (11, 1), (32, 1), (47, 1), (55, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (27, 1), (28, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (28, 1), (48, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (28, 1), (45, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (28, 1), (32, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (32, 1), (41, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (11, 1), (28, 1), (45, 1), (47, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (28, 1), (32, 1), (45, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (32, 1), (41, 1), (47, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (28, 1), (33, 1), (41, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (28, 1), (45, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (28, 1), (32, 1), (35, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (32, 1), (41, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (6, 1), (8, 1), (11, 1), (34, 1), (41, 1), (62, 1), (63, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (8, 1), (11, 1), (34, 1), (41, 1), (47, 1), (62, 1), (63, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (8, 1), (11, 1), (18, 1), (29, 1), (41, 1), (49, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (8, 1), (11, 1), (26, 1), (41, 1), (49, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (8, 1), (11, 1), (41, 1), (62, 1), (64, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (28, 1), (34, 1), (41, 1), (50, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (30, 1), (43, 1), (46, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (31, 1), (41, 1), (51, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (41, 1), (50, 1), (62, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 2), (8, 1), (11, 1), (18, 1), (29, 1), (41, 1), (47, 1), (49, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 2), (8, 1), (11, 1), (26, 1), (41, 1), (47, 1), (49, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 2), (8, 1), (11, 1), (41, 1), (47, 1), (62, 1), (64, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (11, 1), (28, 1), (34, 1), (41, 1), (47, 1), (50, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (11, 1), (30, 1), (43, 1), (46, 1), (47, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (11, 1), (31, 1), (41, 1), (47, 1), (51, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (11, 1), (41, 1), (47, 1), (50, 1), (62, 1), (64, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (33, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (33, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (22, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (22, 1), (28, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (28, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (33, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (33, 1), (41, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (28, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (45, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (33, 1), (41, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (45, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(45, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (44, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (19, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (19, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (11, 1), (19, 1), (47, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (19, 1), (32, 1), (47, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (38, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (11, 1), (27, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (11, 1), (27, 1), (47, 1), (62, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (11, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (11, 1), (47, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (12, 1), (34, 1), (41, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (34, 1), (41, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (11, 1), (12, 1), (34, 1), (41, 1), (47, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (11, 1), (34, 1), (41, 1), (47, 1), (57, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (19, 1), (33, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (11, 1), (22, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (11, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (19, 1), (33, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (24, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (32, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (28, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (19, 1), (28, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (28, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (32, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (32, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (7, 1), (8, 1), (10, 1), (11, 1), (41, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (8, 1), (11, 1), (12, 1), (18, 1), (41, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 2), (8, 1), (10, 1), (11, 1), (41, 1), (47, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 2), (8, 1), (11, 1), (12, 1), (18, 1), (41, 1), (47, 1), (62, 1), (64, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (28, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (47, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (11, 1), (47, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (7, 1), (8, 1), (11, 1), (18, 1), (41, 1), (49, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 2), (8, 1), (11, 1), (18, 1), (41, 1), (47, 1), (49, 1), (62, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (28, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (68, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (41, 1), (51, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (11, 1), (41, 1), (47, 1), (51, 1), (62, 1), (64, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (11, 1), (24, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (24, 1), (47, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (11, 1), (16, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (16, 1), (47, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (31, 1), (41, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (11, 1), (31, 1), (41, 1), (47, 1), (62, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (11, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (11, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (47, 1), (61, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (33, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (33, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (28, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(28, 1), (32, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (11, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (11, 1), (47, 1), (62, 1), (64, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (11, 1), (47, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (32, 1), (47, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (34, 1), (41, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (11, 1), (34, 1), (41, 1), (47, 1), (62, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (11, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (41, 1), (62, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (11, 1), (41, 1), (47, 1), (62, 1), (64, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (43, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (11, 1), (43, 1), (47, 1), (62, 1), (64, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (7, 1), (8, 1), (11, 1), (41, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 2), (8, 1), (11, 1), (41, 1), (47, 1), (62, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (28, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (11, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (47, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (41, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (11, 1), (41, 1), (47, 1), (62, 1), (64, 1), (68, 1)] }]
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
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case574Selected.selectedHasNoCommonZero

end Krenn.X5Case574Selected
