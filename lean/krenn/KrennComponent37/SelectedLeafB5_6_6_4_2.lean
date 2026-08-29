import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_6_6_4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "78d4ec46a8af3da9bed6a1d8702b9919ad594d81df89c98845d690d417b1f1e7"
def certificateSHA256 : String := "7a86706115750912547ecddab57598c3761d46b423fbaff15f9d18b55b8a6701"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 673 := ![
  12,
  13,
  16,
  17,
  300,
  591,
  660,
  661,
  664,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(28, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (63, 1), (64, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_6_6_4_2.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_6_6_4_2
