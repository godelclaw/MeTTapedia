import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB4_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ba3b8141c2976272a31c049606e4ecb936da456008cda04dc208ea2b1f5bacd5"
def certificateSHA256 : String := "883f79b449d4a43830f293487d0d5975c98265f842e44f781235fe07c6cc3728"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 622 := ![
  11,
  14,
  30,
  33,
  204,
  230,
  242,
  245,
  355,
  366,
  562,
  564,
  574,
  579,
  580,
  581,
  590,
  599,
  606,
  607,
  611,
  614,
  616,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (54, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (27, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (50, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (25, 1), (39, 1), (43, 1), (49, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (29, 1), (36, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (38, 1), (43, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (39, 1), (49, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (43, 1), (49, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (36, 1), (49, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (29, 1), (36, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (38, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (49, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (39, 1), (43, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (39, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (43, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (54, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (11, 1), (38, 1), (43, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (49, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (50, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (38, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (38, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (49, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (39, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(39, 1), (54, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (38, 1), (43, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (49, 1), (57, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (36, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (39, 1), (54, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (50, 1), (54, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (38, 1), (43, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (49, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(38, 1), (54, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(27, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(27, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (29, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(22, 1), (38, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (38, 1), (39, 1), (43, 1), (55, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (49, 1), (55, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (55, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(43, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (38, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (29, 1), (33, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (20, 1), (33, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (22, 1), (54, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (27, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (33, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (29, 1), (36, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (29, 1), (39, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (38, 1), (43, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (49, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (29, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (29, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (22, 1), (39, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (27, 1), (39, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (27, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (33, 1), (36, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (25, 1), (39, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (29, 1), (36, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (38, 1), (43, 2), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (39, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (33, 1), (36, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (29, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (49, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB4_7_7.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB4_7_7
