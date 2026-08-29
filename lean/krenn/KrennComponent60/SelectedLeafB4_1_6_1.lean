import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_1_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1a5ac84b4e56a9f551e770797960dfcaabf80e001c5be7d7f5500c4c74d562cd"
def certificateSHA256 : String := "03af48dc9c9fd0a187286e9580bd700a836ad34a7018e1015c90a26103fd72b9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 668 := ![
  24,
  151,
  179,
  194,
  256,
  458,
  578,
  579,
  582,
  600,
  601,
  606,
  612,
  653,
  656,
  659,
  660,
  663,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(0, 1), (49, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (49, 1), (65, 1)] }, { coefficient := -2, powers := [(30, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (36, 1), (55, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (36, 1), (55, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (55, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(33, 1), (36, 1), (65, 1)] }, { coefficient := -2, powers := [(55, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (20, 1), (36, 1), (44, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 2), (30, 1), (36, 2), (44, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 2), (30, 1), (36, 1), (44, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 2), (36, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (20, 2), (58, 1), (61, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (20, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (20, 1), (30, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := 3, powers := [(0, 1), (13, 1), (20, 1), (36, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 3, powers := [(0, 1), (13, 1), (30, 1), (36, 2), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (30, 1), (36, 1), (65, 1)] }, { coefficient := 4, powers := [(0, 1), (20, 2), (36, 1), (44, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 4, powers := [(0, 1), (20, 1), (30, 1), (36, 2), (44, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (30, 1), (36, 1), (44, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (36, 1), (58, 1), (65, 1)] }, { coefficient := 3, powers := [(13, 1), (20, 2), (36, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 3, powers := [(13, 1), (20, 1), (30, 1), (36, 2), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 3), (36, 1), (44, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 2), (30, 1), (36, 2), (44, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 2), (49, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (30, 1), (36, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (33, 1), (36, 1), (49, 1), (65, 1)] }, { coefficient := -2, powers := [(30, 1), (33, 1), (36, 2), (65, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (20, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (36, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (20, 1), (36, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (30, 1), (36, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 2), (36, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (30, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (36, 1), (44, 1), (59, 1)] }, { coefficient := 3, powers := [(0, 1), (13, 1), (36, 1), (59, 1)] }, { coefficient := 4, powers := [(0, 1), (20, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 3, powers := [(13, 1), (20, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(20, 2), (36, 1), (44, 1), (59, 1)] }, { coefficient := -2, powers := [(20, 1), (55, 1)] }, { coefficient := -2, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (20, 2), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (30, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := 2, powers := [(20, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 2, powers := [(20, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (20, 1), (29, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 2, powers := [(20, 1), (29, 1), (36, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(55, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(49, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (36, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := -3, powers := [(0, 1), (13, 1), (36, 1), (45, 1), (59, 1)] }, { coefficient := -4, powers := [(0, 1), (20, 1), (36, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := -3, powers := [(13, 1), (20, 1), (36, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (36, 1), (59, 1)] }, { coefficient := -2, powers := [(20, 2), (36, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(20, 1), (45, 1), (55, 1)] }, { coefficient := 2, powers := [(33, 1), (36, 1), (45, 1)] }, { coefficient := 2, powers := [(42, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (20, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := -2, powers := [(20, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(3, 1), (20, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 2), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (29, 1), (36, 1), (55, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (55, 1)] }, { coefficient := 2, powers := [(6, 1), (33, 1)] }, { coefficient := -2, powers := [(20, 1), (29, 1), (36, 1), (55, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (29, 1), (55, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (29, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(29, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := 2, powers := [(29, 1), (55, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(55, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (20, 1), (29, 1), (36, 1), (44, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 2), (29, 1), (30, 1), (36, 2), (44, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 2), (29, 1), (30, 1), (36, 1), (44, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 2), (29, 1), (36, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (20, 2), (29, 1), (58, 1), (61, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (20, 1), (29, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (20, 1), (29, 1), (30, 1), (36, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (20, 1), (29, 1), (36, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -3, powers := [(0, 1), (13, 1), (29, 1), (30, 1), (36, 2), (59, 1), (65, 1)] }, { coefficient := 3, powers := [(0, 1), (13, 1), (29, 1), (30, 1), (36, 1), (65, 1)] }, { coefficient := -4, powers := [(0, 1), (20, 2), (29, 1), (36, 1), (44, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -4, powers := [(0, 1), (20, 1), (29, 1), (30, 1), (36, 2), (44, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (29, 1), (30, 1), (36, 1), (44, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (29, 1), (36, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 2), (29, 1), (36, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -3, powers := [(13, 1), (20, 1), (29, 1), (30, 1), (36, 2), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (29, 1), (30, 1), (36, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 3), (29, 1), (36, 1), (44, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 2), (29, 1), (30, 1), (36, 2), (44, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 2), (29, 1), (49, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (29, 1), (30, 1), (36, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (29, 1), (33, 1), (36, 1), (49, 1), (65, 1)] }, { coefficient := 2, powers := [(29, 1), (30, 1), (33, 1), (36, 2), (65, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (36, 1), (39, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 3, powers := [(0, 1), (13, 1), (36, 1), (39, 1), (45, 1), (59, 1)] }, { coefficient := 4, powers := [(0, 1), (20, 1), (36, 1), (39, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (30, 1), (36, 1), (40, 1), (44, 1)] }, { coefficient := -2, powers := [(0, 1), (30, 1), (36, 1), (44, 1), (45, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (40, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 2), (20, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (30, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (20, 2), (40, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (20, 2), (45, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (20, 1), (40, 1), (58, 1)] }, { coefficient := 2, powers := [(3, 1), (20, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (20, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (30, 1), (36, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (30, 1), (36, 1), (45, 1), (61, 1)] }, { coefficient := 3, powers := [(13, 1), (20, 1), (36, 1), (39, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 2, powers := [(13, 1), (39, 1)] }, { coefficient := 2, powers := [(20, 2), (36, 1), (39, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := -2, powers := [(20, 1), (30, 1), (36, 1), (40, 1), (44, 1)] }, { coefficient := -2, powers := [(20, 1), (30, 1), (36, 1), (44, 1), (45, 1)] }, { coefficient := -2, powers := [(20, 1), (36, 1), (40, 1), (58, 1)] }, { coefficient := -2, powers := [(20, 1), (36, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(20, 1), (39, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(33, 1), (36, 1), (39, 1), (45, 1)] }, { coefficient := -2, powers := [(39, 1), (42, 1)] }, { coefficient := -2, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (20, 1), (36, 1), (44, 1), (45, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 2), (30, 1), (36, 2), (44, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 2), (30, 1), (36, 1), (44, 1), (45, 1)] }, { coefficient := 2, powers := [(0, 2), (36, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (20, 2), (45, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (20, 1), (45, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (20, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (9, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (20, 1), (30, 1), (36, 1), (45, 1), (61, 1)] }, { coefficient := -3, powers := [(0, 1), (13, 1), (20, 1), (36, 1), (45, 1), (49, 1), (59, 1)] }, { coefficient := -3, powers := [(0, 1), (13, 1), (30, 1), (36, 2), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (30, 1), (36, 1), (45, 1)] }, { coefficient := -4, powers := [(0, 1), (20, 2), (36, 1), (44, 1), (45, 1), (49, 1), (59, 1)] }, { coefficient := -4, powers := [(0, 1), (20, 1), (30, 1), (36, 2), (44, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (30, 1), (36, 1), (44, 1), (45, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (36, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (36, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 2), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 2), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := -2, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 2, powers := [(9, 1), (55, 1), (64, 1)] }, { coefficient := -3, powers := [(13, 1), (20, 2), (36, 1), (45, 1), (49, 1), (59, 1)] }, { coefficient := -3, powers := [(13, 1), (20, 1), (30, 1), (36, 2), (45, 1), (59, 1)] }, { coefficient := -2, powers := [(20, 3), (36, 1), (44, 1), (45, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(20, 2), (30, 1), (36, 2), (44, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(20, 2), (36, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(20, 2), (36, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(20, 2), (36, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(20, 2), (45, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 2, powers := [(20, 1), (30, 1), (36, 1), (45, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (33, 1), (36, 1), (45, 1), (49, 1)] }, { coefficient := 2, powers := [(20, 1), (42, 1), (49, 1)] }, { coefficient := 2, powers := [(30, 1), (33, 1), (36, 2), (45, 1)] }, { coefficient := 2, powers := [(30, 1), (36, 1), (42, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_1_6_1.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_1_6_1
