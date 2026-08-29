import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_7_5_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "91b99db5fe43f4070e8466ccdef61673b71ee451bd668a6acb77ee2c2431d233"
def certificateSHA256 : String := "8a183a33568a514fda529b57da499070f313ea74472b16d175aec2ac5cca457c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 673 := ![
  13,
  17,
  151,
  300,
  302,
  308,
  487,
  499,
  591,
  627,
  660,
  661,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(23, 1), (60, 1), (63, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (43, 1), (60, 1), (63, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (18, 1), (23, 1), (60, 1), (63, 1), (69, 1), (70, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (28, 1), (60, 1), (63, 1), (69, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (60, 1), (63, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (18, 1), (60, 1), (63, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (60, 1), (63, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (60, 1), (63, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(60, 1), (63, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (60, 1), (63, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1), (60, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (23, 1), (30, 1), (60, 1), (63, 1), (69, 1), (70, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (28, 1), (30, 1), (60, 1), (63, 1), (69, 1), (70, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (60, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (43, 1), (60, 1), (63, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (13, 1), (18, 1), (23, 1), (60, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (18, 1), (28, 1), (60, 1), (63, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (23, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (23, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_7_5_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_7_5_6
