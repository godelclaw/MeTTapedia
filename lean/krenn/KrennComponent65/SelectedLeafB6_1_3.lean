import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB6_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "77e443625d1656d469fd5dc6a44b70b20df962acea690118f899f19d2dec21f5"
def certificateSHA256 : String := "9d975d799d26ac0b24c40f5687e7aeb4cf936c10b2fe0d4d080c0c8bb28a3bd2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 671 := ![
  317,
  411,
  412,
  444,
  447,
  581,
  610,
  666,
  667,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(20, 1), (51, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(49, 1), (51, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (51, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (49, 1), (51, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1), (57, 1), (65, 1)] }],
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
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB6_1_3.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB6_1_3
