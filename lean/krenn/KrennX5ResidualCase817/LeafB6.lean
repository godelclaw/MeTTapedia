import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase817.LeafB6

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "6953e75dee66d508fafac8282253a5488f8fbac37f9e3c7e2f490fe77aa6702f"
def sourceSystemSemanticSHA256 : String := "de55eafc3b23db84e079fd3e87676655443e8c8e4751758da94a05b09b017c69"
def certificateSHA256 : String := "b6b9aef0d888f88c16ff01f4099cf72b74212f2da167def0da340df9fc5e4ddd"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 32 → Fin 678 := ![
  2,
  5,
  9,
  12,
  19,
  24,
  25,
  29,
  32,
  33,
  47,
  49,
  336,
  388,
  395,
  397,
  413,
  420,
  422,
  423,
  424,
  425,
  427,
  436,
  439,
  544,
  634,
  664,
  671,
  673,
  674,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 72) := ![
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (15, 1), (47, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (47, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (15, 1), (47, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (47, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (47, 1), (54, 1), (56, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (40, 1), (47, 1), (56, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (43, 1), (47, 1), (56, 1), (66, 1), (71, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (47, 1), (51, 1), (56, 1), (63, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (41, 1), (42, 1), (54, 1), (59, 1), (69, 1), (71, 1)] }, { coefficient := -1, powers := [(7, 1), (47, 1), (54, 1), (56, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (40, 1), (41, 1), (42, 1), (59, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (41, 1), (42, 1), (51, 1), (59, 1), (63, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (47, 1), (56, 1), (69, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (47, 1), (56, 1), (66, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (47, 1), (51, 1), (56, 1), (63, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (42, 1), (45, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (40, 1), (42, 1), (45, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (42, 1), (45, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (43, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (33, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (33, 1), (40, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (34, 1), (42, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (34, 1), (40, 1), (42, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (34, 1), (42, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (28, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (15, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (54, 1), (56, 1), (69, 1), (71, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (40, 1), (56, 1), (69, 1), (71, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (43, 1), (56, 1), (66, 1), (71, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (51, 1), (56, 1), (63, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (57, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (40, 1), (42, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(33, 1), (40, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (56, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (56, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (56, 1), (66, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (56, 1), (63, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (15, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (42, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (34, 1), (40, 1), (42, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (34, 1), (42, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (34, 1), (41, 1), (42, 1), (54, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (54, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (34, 1), (40, 1), (41, 1), (42, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (34, 1), (41, 1), (42, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (40, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (43, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (51, 1), (56, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase817.LeafB6.selectedHasNoCommonZero

end Krenn.X5ResidualCase817.LeafB6
