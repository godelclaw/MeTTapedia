import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_0_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b18b5f45f5d485fa976a277effcaec2b5c5ccd6d822af8b498ec22c075aa35bd"
def certificateSHA256 : String := "ac3a7b84d2f124ae37893b1488be834188b7efc80c60a2b0df5261692b454b6e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 667 := ![
  175,
  176,
  310,
  411,
  424,
  431,
  530,
  608,
  660,
  662,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(25, 1), (29, 1), (47, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (47, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (29, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (29, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (29, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (29, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (47, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (25, 1), (36, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (26, 1), (36, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (44, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (28, 1), (44, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (25, 1), (29, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (26, 1), (29, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 2), (29, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (26, 1), (29, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (28, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (28, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1), (66, 1)] }],
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
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_0_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_0_7
