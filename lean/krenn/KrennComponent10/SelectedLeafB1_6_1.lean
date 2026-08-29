import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB1_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dfcabf34078b17bd65d69a33ec4a658bafebb52fa29c1f2cda65c3ce237d03cd"
def certificateSHA256 : String := "868dc5da43b5f4b3b09e591015729dff7a6bb5be634a5f96e751a9e1482ab618"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 4 → Fin 644 := ![
  196,
  473,
  635,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 4 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 4 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(43, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1), (63, 1)] }],
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
    ¬ ∀ index : Fin 4,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB1_6_1.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB1_6_1
