import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_6_4_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "509be7a93a8c78831ae1f2efb1adf85e533967a9d6dace3fefe1e2411ddfc4a7"
def certificateSHA256 : String := "768f779c413f4b407f7689d16b3368b7fb2997866fe9a34c58b689489101d290"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 13 → Fin 676 := ![
  5,
  298,
  299,
  505,
  519,
  604,
  605,
  656,
  659,
  667,
  668,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 13 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 13 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(4, 1), (52, 1), (71, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (71, 1)] }, { coefficient := -1, powers := [(4, 1), (68, 1), (71, 1)] }, { coefficient := 1, powers := [(7, 1), (41, 1), (71, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (38, 1), (71, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (52, 1), (70, 1)] }, { coefficient := -1, powers := [(4, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(4, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (25, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(4, 1), (46, 1), (52, 1), (70, 1)] }, { coefficient := 1, powers := [(4, 1), (46, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(4, 1), (46, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (60, 1), (71, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (48, 1), (71, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (68, 1)] }, { coefficient := 2, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (38, 1)] }]
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
    ¬ ∀ index : Fin 13,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_6_4_2_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_6_4_2_3
