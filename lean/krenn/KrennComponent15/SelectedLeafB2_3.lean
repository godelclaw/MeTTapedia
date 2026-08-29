import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e3f077a59832426dfe25ccd2e5853f10aeed0751ab000c5026da54abbc3a5d91"
def certificateSHA256 : String := "5a27cd085e510bd70ffadc49f85ecbfc979e6135b1a0a836079d6cf706abe469"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 5 → Fin 592 := ![
  3,
  476,
  586,
  587,
  591
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(18, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(43, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1), (59, 1)] }],
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB2_3.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB2_3
