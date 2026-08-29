import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB0_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "19f21898947690bdbbdb241702551767602afba64ec0b1a0d34fbd58449194ea"
def certificateSHA256 : String := "96edaadb2c15632a4d6e299acf6160837b0b968b45e29c947ae041bf8c9ebcf9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 667 := ![
  471,
  475,
  609,
  646,
  658,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }, { coefficient := 1, powers := [(41, 1), (50, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (35, 1), (41, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(38, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(44, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (41, 1), (62, 1)] }],
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB0_6_1.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB0_6_1
