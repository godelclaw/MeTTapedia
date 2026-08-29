import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9d29c01236681ee2014245b0e9e356c32e09b21f40ac8dd56b7e01577792e8f1"
def certificateSHA256 : String := "c0177d1648352c8e0db0c659ea487d82bb68043b5132cba53dd6a1c3d949276b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 8 → Fin 667 := ![
  71,
  153,
  221,
  303,
  583,
  661,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 8 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 8 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(44, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 8,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_4_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_4_5
