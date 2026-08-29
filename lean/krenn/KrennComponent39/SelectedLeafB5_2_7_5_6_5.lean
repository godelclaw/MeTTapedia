import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_7_5_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d0c987a38837c5664e371a867d5ffeecc6114d21b934d6e8a2e899b14b5693c4"
def certificateSHA256 : String := "d8f17b7dbf44a7b0c90e39dca79d6c3684797ee1397d27c5fddaa949ec1631be"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 679 := ![
  10,
  14,
  26,
  232,
  280,
  304,
  305,
  603,
  659,
  662,
  669,
  671,
  677,
  678
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(4, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(7, 1), (39, 1), (72, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (72, 1)] }, { coefficient := -1, powers := [(14, 1), (36, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (51, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (42, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (42, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (42, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }]
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
    (values : Fin 73 → R) :
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_7_5_6_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_7_5_6_5
