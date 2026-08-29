import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "700a697ce3528a2ffaf6c2f8f4fc307fd4ee24d6937b8bedbd6ccc9fa5737dda"
def certificateSHA256 : String := "52bbef99bb600f23c8ec4f9d48e7712d0c256e4d3c67b65d64c46cbf83bae375"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 641 := ![
  0,
  2,
  4,
  5,
  19,
  24,
  25,
  27,
  29,
  32,
  68,
  161,
  162,
  163,
  164,
  168,
  169,
  170,
  184,
  189,
  192,
  359,
  360,
  361,
  363,
  364,
  406,
  409,
  463,
  466,
  517,
  550,
  557,
  582,
  634,
  635,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (55, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (23, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (32, 1), (48, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (27, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (38, 1), (55, 1), (58, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (38, 1), (58, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (6, 1), (48, 1), (53, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (48, 1), (53, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (48, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (36, 1), (48, 1), (53, 1), (58, 1), (60, 1), (64, 2)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (47, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (48, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(18, 1), (27, 1), (47, 1), (53, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (52, 1), (59, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (18, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (53, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (59, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (27, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (27, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (36, 1), (53, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(12, 1), (27, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (48, 1), (53, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (45, 1), (59, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (41, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(18, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (55, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (59, 1)] }, { coefficient := -2, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(53, 1)] }],
  [{ coefficient := 2, powers := [(48, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (53, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (38, 1), (41, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (36, 1), (48, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 2), (55, 1), (64, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := -2, powers := [(18, 1), (27, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (45, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (24, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (24, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (24, 1), (48, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (24, 1), (48, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (32, 1), (36, 1), (48, 1), (53, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (28, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (24, 1), (35, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (24, 1), (35, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (27, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (36, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (36, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (27, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (27, 1), (47, 1), (53, 1), (60, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB5_7.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB5_7
