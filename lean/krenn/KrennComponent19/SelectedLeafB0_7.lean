import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB0_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7ec3fc220ff1f23bf751fce0992554a1d1cf270d18ffb942d2ad06462543201e"
def certificateSHA256 : String := "baf14574f8861beb1d3df050def16542afbe91f055848198bfc653bdf4521159"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 669 := ![
  10,
  18,
  20,
  22,
  24,
  33,
  198,
  200,
  203,
  304,
  318,
  420,
  424,
  429,
  565,
  610,
  662,
  663,
  665,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (35, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (38, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (38, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(13, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := 1, powers := [(44, 1), (58, 1)] }, { coefficient := -1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (35, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (27, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (27, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (46, 1), (54, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB0_7.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB0_7
