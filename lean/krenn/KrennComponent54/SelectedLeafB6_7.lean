import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component54.SelectedLeafB6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5af8587b219861d565b7cb483c66fec681571803dd44384a1929fd1d7d7cf2b7"
def certificateSHA256 : String := "c2cca6a952844a1dd598bbb13bb907552a3dce09e497e3bc01fbbd272b262637"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 645 := ![
  9,
  11,
  16,
  17,
  22,
  186,
  195,
  196,
  197,
  198,
  202,
  204,
  223,
  234,
  235,
  288,
  348,
  349,
  350,
  351,
  352,
  359,
  360,
  364,
  366,
  384,
  385,
  468,
  474,
  517,
  560,
  561,
  586,
  587,
  638,
  641,
  643,
  644
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (30, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (30, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (36, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (26, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (26, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (33, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (33, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (25, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (25, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (33, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (33, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (36, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(25, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (41, 1), (48, 1)] }, { coefficient := -1, powers := [(30, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(30, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1), (65, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (42, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (44, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (37, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (26, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (26, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (21, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (21, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (37, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (21, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (21, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (42, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(52, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (42, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (42, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (48, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (48, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (39, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (39, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (42, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (42, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (48, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (48, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (39, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (39, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (42, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (42, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (48, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (48, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (41, 1), (42, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (42, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (36, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (56, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component54.SelectedLeafB6_7.selectedHasNoCommonZero

end Krenn.Component54.SelectedLeafB6_7
