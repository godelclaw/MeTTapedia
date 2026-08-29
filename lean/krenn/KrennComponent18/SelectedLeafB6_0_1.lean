import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_0_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "785b7308a0fa66798dc5754df1b285728042ac07d1e3b9cf4ae53a619349d08c"
def certificateSHA256 : String := "84ecaa1ff306dde9dc2eaf24a8ad814c38354d8ce43de8597dea3125c80d1e03"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 9 → Fin 667 := ![
  323,
  426,
  458,
  463,
  581,
  609,
  662,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 9 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 9 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (45, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (47, 1), (63, 1)] }],
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 9,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_0_1.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_0_1
