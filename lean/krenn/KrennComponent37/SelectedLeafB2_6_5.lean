import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB2_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "beb1ee605aae589ec0fdda13f4e21f189d82bf8d591c220e5478805f615ae9c9"
def certificateSHA256 : String := "cb74ebabe09f510d4973d6d1d4237f1b1e013c9e55a2ce5027cd01a2c72d0653"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 667 := ![
  472,
  475,
  608,
  645,
  658,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(44, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (38, 1), (44, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (41, 1), (44, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1), (46, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(41, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(44, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (66, 1)] }],
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB2_6_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB2_6_5
