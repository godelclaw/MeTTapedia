import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1f436f7992c30c31d017903f9e46f4e0cc79bd98f8ea9d3180db6bd3775e9c4c"
def certificateSHA256 : String := "30d9e7880fe80d609ccc49e70477fe402a548fd8b9899b84e799255eb23d5722"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 673 := ![
  22,
  29,
  30,
  31,
  190,
  191,
  193,
  196,
  300,
  318,
  350,
  424,
  425,
  427,
  433,
  439,
  440,
  451,
  463,
  465,
  482,
  566,
  570,
  625,
  645,
  650,
  660,
  661,
  663,
  665,
  666,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (57, 1), (62, 2), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (57, 1), (62, 2), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (24, 1), (45, 1), (51, 1), (59, 1), (62, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (24, 1), (45, 1), (56, 1), (59, 1), (62, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (45, 1), (53, 1), (59, 1), (62, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (35, 1), (45, 1), (51, 1), (59, 1), (62, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (35, 1), (45, 1), (56, 1), (59, 1), (62, 1), (64, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (35, 1), (45, 1), (53, 1), (59, 1), (62, 1), (64, 1), (67, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (3, 1), (19, 1), (54, 1), (57, 1), (59, 1), (61, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (21, 1), (54, 1), (57, 1), (59, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (24, 1), (27, 1), (49, 1), (57, 1), (59, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (22, 1), (23, 1), (52, 1), (57, 1), (59, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (22, 1), (49, 1), (57, 1), (59, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (59, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (59, 1), (62, 1), (67, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 2), (3, 1), (49, 1), (57, 2), (59, 1), (61, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 2), (3, 1), (23, 1), (49, 1), (57, 2), (59, 1), (61, 1), (62, 1), (67, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 2), (3, 1), (54, 1), (57, 1), (59, 1), (61, 1), (62, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 2), (3, 1), (24, 1), (49, 1), (57, 1), (59, 1), (61, 1), (62, 1), (67, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (54, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (24, 1), (49, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (16, 1), (47, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (42, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (12, 1), (42, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (42, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (8, 1), (22, 1), (52, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (42, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (42, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (35, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (45, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (45, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (45, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(35, 1), (45, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (47, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (45, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (45, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (24, 1), (45, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (35, 1), (45, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (17, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (8, 1), (22, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (21, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (3, 1), (57, 2), (59, 1), (61, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1), (62, 2), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (12, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (3, 1), (57, 1), (59, 1), (61, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(35, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (3, 1), (37, 1), (57, 1), (59, 1), (60, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (57, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (34, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (35, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 2), (3, 1), (57, 2), (59, 1), (61, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 2), (3, 1), (23, 1), (57, 2), (59, 1), (61, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 2), (3, 1), (24, 1), (42, 1), (57, 1), (59, 1), (61, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 2), (3, 1), (57, 2), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (8, 1), (34, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 2), (3, 1), (46, 1), (49, 1), (57, 2), (59, 1), (61, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 2), (3, 1), (47, 1), (54, 1), (57, 1), (59, 1), (61, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 2), (3, 1), (19, 1), (42, 1), (54, 1), (57, 1), (59, 1), (61, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 2), (3, 1), (23, 1), (46, 1), (49, 1), (57, 2), (59, 1), (61, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 2), (3, 1), (24, 1), (47, 1), (49, 1), (57, 1), (59, 1), (61, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (21, 1), (42, 1), (54, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (24, 1), (27, 1), (42, 1), (49, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (22, 1), (23, 1), (42, 1), (52, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (22, 1), (42, 1), (49, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (21, 1), (57, 1), (62, 2), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (26, 1), (57, 1), (62, 2), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (21, 1), (24, 1), (45, 1), (51, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (21, 1), (24, 1), (45, 1), (56, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (21, 1), (45, 1), (53, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (42, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (42, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (24, 1), (35, 1), (45, 1), (51, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (24, 1), (35, 1), (45, 1), (56, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (35, 1), (45, 1), (53, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (5, 1), (42, 1), (44, 1), (49, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (12, 1), (42, 1), (46, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (12, 1), (47, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (16, 1), (47, 1), (49, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (17, 1), (46, 1), (49, 1), (57, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 2), (16, 1), (45, 1), (59, 2), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (35, 1), (45, 1), (59, 2), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (42, 1), (44, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (44, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (42, 1), (44, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (35, 1), (44, 1), (59, 1), (62, 1), (64, 1), (67, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_7_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_7_6
