import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_6_7_5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3347deaf94369a458dea44072094e51b36fc5a8043b1799f8313eda6c7a53520"
def certificateSHA256 : String := "92ba78bdd295b63ca10b829a80e1a53c1eb7fa544b00330d9c9c6aca461ffbdc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 4 → Fin 678 := ![
  463,
  486,
  665,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 4 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 4 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (30, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (63, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 4,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_6_7_5_1.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_6_7_5_1
