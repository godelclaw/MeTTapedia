import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_1_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c9de6a0f809787a09d63de27f30b93c425c80b89cfb6b54b7e37dbdadaf0c2d6"
def certificateSHA256 : String := "fbe7dc879f264c24957300713a2c0f14271ddaebd950fe9675e3fda41694adac"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 12 → Fin 667 := ![
  3,
  294,
  424,
  427,
  466,
  475,
  581,
  608,
  659,
  662,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 12 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 12 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (47, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (44, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (26, 1), (47, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 12,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_1_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_1_1
