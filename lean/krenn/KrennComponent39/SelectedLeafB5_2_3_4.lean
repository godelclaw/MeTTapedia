import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f6a10d01d820036df5e428fab116d1133031bcb8fb25b02970ffe2e02de1982d"
def certificateSHA256 : String := "d9d568c9e7f117e9f74124bd9bbe4f57667cefac42b93a7346ece7a5ef87d8dc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 48 → Fin 673 := ![
  14,
  26,
  62,
  187,
  188,
  232,
  276,
  280,
  300,
  304,
  305,
  316,
  318,
  319,
  342,
  394,
  396,
  397,
  416,
  422,
  426,
  439,
  441,
  452,
  472,
  478,
  482,
  487,
  502,
  511,
  532,
  562,
  570,
  580,
  581,
  602,
  603,
  644,
  649,
  659,
  661,
  662,
  663,
  665,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 48 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 48 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (33, 1), (36, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (42, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (42, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (42, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (39, 1), (42, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (42, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (42, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (39, 1), (42, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (42, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(4, 1), (42, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (42, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (42, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (39, 1), (42, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (39, 1), (42, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (42, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (42, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(10, 1), (35, 1), (42, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (35, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (42, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (42, 1), (59, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (36, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (24, 1), (42, 1), (44, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (24, 1), (42, 1), (51, 2), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (24, 1), (42, 1), (51, 1), (56, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (42, 1), (44, 1), (53, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (42, 1), (51, 1), (53, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (42, 1), (53, 1), (56, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (51, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (51, 2), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (51, 1), (56, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (44, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (44, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (51, 3), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (26, 1), (51, 2), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (51, 1), (56, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (51, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (53, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (33, 1), (36, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (27, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (39, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (39, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(4, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (39, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (39, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(10, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (35, 1), (59, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (24, 1), (44, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (24, 1), (51, 2), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (24, 1), (51, 1), (56, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (44, 1), (53, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (51, 1), (53, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (53, 1), (56, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (51, 2), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (51, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (51, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (53, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (23, 1), (44, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (23, 1), (51, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (23, 1), (53, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (24, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (24, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (24, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(21, 1), (23, 1), (24, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (23, 1), (24, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (16, 1), (18, 1), (42, 1), (44, 2), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (18, 1), (42, 1), (44, 1), (51, 2), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (18, 1), (42, 1), (44, 1), (51, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (42, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (23, 1), (42, 1), (44, 2), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (23, 1), (42, 1), (44, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (23, 1), (42, 1), (44, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (42, 1), (44, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (42, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (42, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (24, 1), (42, 1), (51, 1), (62, 1), (65, 2)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (24, 1), (42, 1), (56, 1), (62, 1), (65, 2)] }],
  [{ coefficient := 2, powers := [(2, 1), (24, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (24, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (44, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (51, 2), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (51, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (27, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (27, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (27, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (44, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (24, 1), (44, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (24, 1), (51, 2), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (24, 1), (51, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (44, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (51, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (53, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (44, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (44, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (27, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (27, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (27, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (26, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (26, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (26, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (23, 1), (44, 2), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (23, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (23, 1), (44, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (26, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (26, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (26, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (16, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (23, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (23, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (23, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (23, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (35, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (23, 1), (44, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (23, 1), (51, 2), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (23, 1), (51, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(21, 1), (23, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (16, 1), (18, 1), (44, 2), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (18, 1), (44, 1), (51, 2), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (18, 1), (44, 1), (51, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (44, 2), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (44, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (44, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (44, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (24, 1), (51, 1), (62, 1), (65, 2)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (24, 1), (56, 1), (62, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (27, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (27, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (27, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (35, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (24, 1), (42, 1), (44, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (24, 1), (42, 1), (51, 2), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (24, 1), (42, 1), (51, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (42, 1), (44, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (42, 1), (51, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (42, 1), (53, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (44, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (39, 1), (56, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (45, 1), (53, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(35, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (44, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (39, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (44, 1), (51, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := -1, powers := [(35, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (16, 1), (18, 1), (27, 1), (44, 2), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (18, 1), (27, 1), (44, 1), (51, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (18, 1), (27, 1), (44, 1), (51, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (20, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (20, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (27, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (23, 1), (27, 1), (44, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (23, 1), (27, 1), (44, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (23, 1), (27, 1), (44, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (20, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (20, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (20, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (30, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (20, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (23, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (23, 1), (44, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (20, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (20, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (23, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (23, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (59, 1), (66, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (24, 1), (27, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (24, 1), (27, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (35, 1), (59, 2)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (59, 2)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (44, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (35, 1), (39, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (16, 1), (18, 1), (42, 1), (44, 3), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (18, 1), (42, 1), (44, 2), (51, 2), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (18, 1), (42, 1), (44, 2), (51, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (18, 1), (44, 2), (45, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (18, 1), (44, 1), (45, 1), (51, 2), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (18, 1), (44, 1), (45, 1), (51, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (42, 1), (44, 2), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (44, 1), (45, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (42, 1), (44, 3), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (42, 1), (44, 2), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (42, 1), (44, 2), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (23, 1), (44, 2), (45, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (23, 1), (44, 1), (45, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (23, 1), (44, 1), (45, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (42, 1), (44, 2), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (42, 1), (44, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (42, 1), (44, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (44, 1), (45, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (45, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (45, 1), (56, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (42, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (24, 1), (42, 1), (44, 1), (51, 1), (62, 1), (65, 2)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (24, 1), (42, 1), (44, 1), (56, 1), (62, 1), (65, 2)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (24, 1), (45, 1), (51, 1), (62, 1), (65, 2)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (24, 1), (45, 1), (56, 1), (62, 1), (65, 2)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 48,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_3_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_3_4
