import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_3_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "07e3d2c75c867fc171854ac6aca413660321fe1cac3d5037fd4449aab6352d10"
def certificateSHA256 : String := "97b71f668fc29e37a93a6723b0c70ad5325f70e8fd3b1483d48900d3e1c6f38d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 676 := ![
  14,
  26,
  65,
  82,
  171,
  173,
  232,
  280,
  304,
  305,
  318,
  439,
  441,
  511,
  515,
  537,
  580,
  602,
  603,
  649,
  659,
  662,
  663,
  669,
  670,
  671,
  672,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (24, 1), (30, 1), (39, 3), (44, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (24, 1), (30, 1), (39, 2), (44, 1), (51, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (20, 1), (24, 1), (30, 1), (39, 3), (59, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (20, 1), (24, 1), (30, 1), (39, 2), (51, 1), (59, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (24, 1), (30, 1), (39, 3), (44, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (24, 1), (30, 1), (39, 2), (44, 1), (51, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (24, 1), (30, 1), (39, 2), (51, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (24, 1), (30, 1), (39, 1), (51, 2), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (30, 2), (36, 1), (39, 2), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (30, 2), (36, 1), (39, 1), (44, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (30, 2), (36, 1), (39, 1), (51, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (30, 2), (36, 1), (39, 1), (56, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (30, 1), (36, 1), (65, 1)] }, { coefficient := -2, powers := [(24, 1), (30, 1), (39, 1), (44, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (44, 2), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (44, 1), (56, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (14, 1), (30, 1), (39, 2), (42, 1), (59, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (30, 1), (39, 1), (42, 1), (51, 1), (59, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (42, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (30, 1), (39, 3), (59, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (30, 1), (39, 2), (51, 1), (59, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (33, 1), (39, 4), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (33, 1), (39, 3), (51, 1), (68, 1), (69, 1)] }, { coefficient := 2, powers := [(30, 1), (39, 1), (59, 1), (66, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (59, 1), (66, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1), (59, 1), (66, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (66, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (30, 1), (39, 3), (59, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (30, 1), (39, 2), (51, 1), (59, 1), (68, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (30, 1), (39, 3), (59, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (30, 1), (39, 2), (51, 1), (59, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (39, 2), (59, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (39, 1), (51, 1), (59, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 2), (36, 1), (39, 1), (59, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 2), (39, 2), (56, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 2), (39, 1), (51, 1), (56, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (33, 1), (39, 3), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (33, 1), (39, 2), (51, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (39, 4), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (39, 3), (51, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (20, 1), (30, 1), (39, 3), (44, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (20, 1), (30, 1), (39, 2), (44, 1), (51, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (30, 1), (39, 3), (59, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (30, 1), (39, 2), (51, 1), (59, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (30, 1), (39, 3), (44, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (30, 1), (39, 2), (44, 1), (51, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (30, 1), (39, 2), (51, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (30, 1), (39, 1), (51, 2), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 2), (36, 1), (39, 2), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 2), (36, 1), (39, 1), (44, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 2), (36, 1), (39, 1), (51, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 2), (36, 1), (39, 1), (56, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (65, 1)] }, { coefficient := 2, powers := [(30, 1), (39, 1), (44, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 2), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (56, 1), (65, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (14, 1), (30, 1), (39, 2), (59, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (30, 1), (39, 1), (51, 1), (59, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (23, 1), (30, 1), (39, 4), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (30, 1), (39, 3), (51, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (39, 3), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (39, 1), (51, 2), (68, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (39, 2), (44, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (39, 2), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (39, 1), (44, 1), (51, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (39, 1), (51, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (39, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (51, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (27, 1), (30, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (53, 1), (67, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (39, 3), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (39, 2), (51, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (39, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (44, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (56, 1), (67, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (39, 3), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (39, 2), (51, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (14, 1), (20, 1), (30, 1), (39, 3), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (20, 1), (30, 1), (39, 2), (51, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (30, 1), (39, 3), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (30, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 2), (36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (14, 1), (30, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (30, 1), (39, 1), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (30, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (39, 1), (51, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (30, 1), (39, 4), (44, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (30, 1), (39, 3), (44, 1), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (39, 2), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (39, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (39, 3), (44, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (39, 3), (56, 1), (68, 1)] }, { coefficient := 2, powers := [(14, 1), (30, 1), (39, 2), (51, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (39, 1), (44, 1), (51, 2), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (39, 1), (51, 2), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (39, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (44, 1), (51, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (14, 1), (20, 1), (30, 1), (39, 3), (44, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (14, 1), (20, 1), (30, 1), (39, 2), (44, 1), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (20, 1), (30, 1), (39, 2), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (20, 1), (30, 1), (39, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (14, 1), (20, 1), (30, 1), (39, 3), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (14, 1), (20, 1), (30, 1), (39, 2), (51, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (18, 1), (20, 1), (30, 1), (39, 3), (44, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (18, 1), (20, 1), (30, 1), (39, 2), (44, 1), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (20, 1), (30, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (20, 1), (30, 1), (39, 1), (51, 2), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (30, 2), (36, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (30, 2), (36, 1), (39, 1), (44, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (30, 2), (36, 1), (39, 1), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (30, 2), (36, 1), (39, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (36, 1)] }, { coefficient := -2, powers := [(10, 1), (30, 1), (39, 1), (44, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (44, 2), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (44, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (30, 1), (39, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (44, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (14, 1), (30, 1), (39, 2), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (30, 1), (39, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (30, 1), (39, 3), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (30, 1), (39, 2), (44, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (30, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (30, 1), (39, 2), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (30, 1), (39, 1), (44, 1), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (30, 1), (39, 1), (51, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 2), (30, 1), (39, 3), (68, 1)] }, { coefficient := 1, powers := [(14, 2), (30, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (30, 1), (39, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (44, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1), (59, 1), (68, 1)] }, { coefficient := 2, powers := [(10, 1), (30, 1), (39, 1), (44, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (44, 2), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (44, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (39, 1), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (39, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (44, 1), (51, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (14, 1), (18, 1), (20, 1), (30, 1), (39, 3), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (18, 1), (20, 1), (30, 1), (39, 2), (51, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (20, 1), (23, 1), (30, 1), (39, 3), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (20, 1), (23, 1), (30, 1), (39, 2), (51, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (20, 1), (30, 1), (39, 2), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (20, 1), (30, 1), (39, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (23, 1), (30, 1), (33, 1), (39, 4), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (23, 1), (30, 1), (33, 1), (39, 3), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (30, 2), (36, 1), (39, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (30, 2), (39, 2), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (30, 2), (39, 1), (51, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (30, 1), (33, 1), (39, 3), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (30, 1), (33, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (23, 1), (30, 1), (39, 1), (59, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (30, 1), (44, 1), (59, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (30, 1), (56, 1), (59, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (33, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (30, 1), (39, 2), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (30, 1), (39, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (30, 2), (36, 1), (39, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (30, 2), (39, 2), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (30, 2), (39, 1), (51, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (30, 1), (33, 1), (39, 3), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (30, 1), (33, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_3_5_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_3_5_3
