import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB4_3_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "34c61d49fa64f95e88c07f1d38b3f3101834f75c25a7b566bb3c22e29f311b72"
def certificateSHA256 : String := "e181c3ed40dead4ff739da96b00bfdf0cc0fbca500757dfaad4851104ff2dcf6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 668 := ![
  1,
  14,
  21,
  169,
  170,
  188,
  267,
  293,
  300,
  312,
  406,
  430,
  435,
  439,
  450,
  579,
  655,
  656,
  658,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (19, 1), (29, 1), (59, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (54, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (12, 1), (29, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (41, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (66, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (29, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (48, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (19, 1), (22, 1), (29, 1), (59, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (23, 1), (54, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (29, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (16, 1), (23, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (29, 1), (41, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (29, 1), (48, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (23, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (29, 1), (40, 1), (41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (19, 1), (29, 1), (43, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB4_3_6_1.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB4_3_6_1
