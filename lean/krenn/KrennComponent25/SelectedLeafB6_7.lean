import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a3599df0a24df0d30b1b22579e570b68722c8ef124c99dceb94ad9ae3ba11a7f"
def certificateSHA256 : String := "0d414cb9fc9334b4584dcaf150a16a06b59685bb1eaf3d838d1e6c65368a6bcb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 662 := ![
  1,
  7,
  12,
  21,
  26,
  75,
  145,
  148,
  152,
  169,
  173,
  188,
  300,
  312,
  450,
  478,
  587,
  655,
  657,
  658,
  659,
  660,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (41, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (41, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (41, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (23, 1), (41, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (41, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (41, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (41, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (41, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (41, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (41, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (41, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (41, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1), (45, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (41, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (41, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (39, 1), (41, 1), (57, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (41, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (41, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (39, 1), (41, 1), (57, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (41, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (38, 1), (41, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(41, 2), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (41, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (41, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (41, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB6_7.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB6_7
