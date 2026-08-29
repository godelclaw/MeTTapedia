import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB4_2_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bef0de148fa8b1c496333763e587c39aa06f9e1663c46a243753c41f1dc3f61b"
def certificateSHA256 : String := "ab6a4acaf7acc5ffd2b2d77f3c29f0ad72046101d05412adc8190db827215fdc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 12 → Fin 668 := ![
  14,
  168,
  300,
  312,
  430,
  435,
  450,
  655,
  658,
  661,
  664,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 12 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 12 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (35, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 4, powers := [(5, 1), (16, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (35, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (23, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (12, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (54, 2)] }, { coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := -4, powers := [(5, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 4, powers := [(5, 1), (8, 1), (35, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (17, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 6, powers := [(5, 1), (35, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (48, 1), (54, 2)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -4, powers := [(5, 1), (8, 1), (29, 1), (35, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (35, 2), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 2, powers := [(5, 2), (32, 1), (35, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (12, 1), (23, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (35, 1), (54, 1), (60, 1)] }, { coefficient := -4, powers := [(5, 1), (8, 1), (35, 1), (47, 1), (50, 1), (60, 1)] }, { coefficient := 4, powers := [(5, 1), (12, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (12, 1), (35, 1), (48, 1), (54, 1)] }, { coefficient := -4, powers := [(5, 1), (16, 1), (35, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (35, 1), (48, 1), (50, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (17, 1), (35, 1), (47, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(17, 1), (47, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 12,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB4_2_6_4.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB4_2_6_4
