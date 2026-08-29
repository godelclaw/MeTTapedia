import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case826Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "1fae9387953e1ffe701ed889ce00b5442bbd0cf109cc411e85d5ba44ea3128c5"
def sourceSystemSemanticSHA256 : String := "6b2127b08892ebcb6637075e8bf998f211c1bc14f17dfd2c3d6f62cfdb79e038"
def certificateSHA256 : String := "8eb325913046dda3cf681a1a5e1b07770091bebe2c1a4247882e20ebf60c59b2"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 37 → Fin 675 := ![
  0,
  1,
  2,
  10,
  12,
  26,
  27,
  29,
  32,
  33,
  34,
  49,
  182,
  384,
  397,
  415,
  416,
  418,
  419,
  420,
  422,
  424,
  425,
  505,
  527,
  536,
  539,
  541,
  601,
  612,
  638,
  658,
  661,
  668,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (35, 1), (68, 1)] }, { coefficient := 1, powers := [(35, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(35, 1), (68, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (39, 1), (69, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (42, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (36, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (22, 1), (28, 1), (36, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (28, 1), (32, 1), (36, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (28, 1), (36, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (41, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (28, 1), (32, 1), (36, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (41, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (10, 1), (15, 1), (28, 1), (29, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (15, 1), (29, 1), (33, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (26, 1), (28, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (26, 1), (33, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (28, 1), (29, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (29, 1), (33, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (28, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (29, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (33, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(28, 1), (29, 1), (34, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (39, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(29, 1), (33, 1), (34, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (39, 1), (43, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (19, 1), (28, 1), (36, 1), (50, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (14, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (21, 1), (28, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (21, 1), (33, 1), (43, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (28, 1), (29, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (29, 1), (33, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (28, 1), (31, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (31, 1), (33, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (28, 1), (29, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (28, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (29, 1), (33, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (33, 1), (43, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (31, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (33, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (33, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (28, 1), (36, 1), (45, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (32, 1), (36, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 2), (21, 1), (28, 1), (43, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 2), (21, 1), (33, 1), (43, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 2), (28, 1), (29, 1), (40, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 2), (29, 1), (33, 1), (40, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (28, 1), (31, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (31, 1), (33, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (28, 1), (29, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (28, 1), (43, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (29, 1), (33, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (33, 1), (43, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (31, 1), (40, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (33, 1), (40, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (36, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (36, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(28, 1), (32, 1), (36, 1), (38, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (27, 1), (36, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (27, 1), (42, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (28, 1), (36, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (32, 1), (35, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (32, 1), (35, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (22, 1), (28, 1), (36, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (16, 1), (22, 1), (28, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (28, 1), (32, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (22, 1), (28, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (22, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (28, 1), (29, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (29, 1), (33, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(21, 1), (22, 1), (28, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(21, 1), (22, 1), (31, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (28, 1), (29, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (28, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (29, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (28, 1), (31, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (10, 1), (15, 1), (21, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (15, 1), (21, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (18, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (18, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (21, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (21, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (33, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (28, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (28, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (36, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (42, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (35, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (35, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (36, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (10, 1), (15, 1), (28, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (15, 1), (33, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (28, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (33, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (37, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (28, 1), (29, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (28, 1), (36, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (42, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (36, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (35, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (35, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (28, 1), (36, 1), (67, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1), (32, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (21, 1), (28, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (29, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (33, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (29, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (29, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (28, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(21, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }]
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

#print axioms Krenn.X5Case826Selected.selectedHasNoCommonZero

end Krenn.X5Case826Selected
