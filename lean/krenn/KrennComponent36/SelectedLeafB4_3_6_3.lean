import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_3_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "652061d1fc37dbb21e02ce74ff3c1d06234b83c0aa092dbdebf9572e04a17073"
def certificateSHA256 : String := "cbc4d2872d34c258e4c430c4e559035c9c85217f2772c670a6db606ae32a6ee9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 675 := ![
  15,
  16,
  19,
  156,
  272,
  305,
  307,
  448,
  451,
  595,
  662,
  665,
  667,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (40, 1), (48, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (40, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (40, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (41, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (40, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (48, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(41, 1), (46, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (40, 2), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1), (41, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (40, 1), (41, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (38, 1), (40, 2), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (40, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1), (40, 1), (63, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_3_6_3.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_3_6_3
