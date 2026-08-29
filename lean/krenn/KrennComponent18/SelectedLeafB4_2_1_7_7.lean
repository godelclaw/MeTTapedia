import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_2_1_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "182ea5d2c8a616e2b08647a7cb35397684a8e776805deb28fb98d47f35be47ea"
def certificateSHA256 : String := "d618a7a0b26332419776cf26235660da4bd6634917fd2c5ac50db0b4641a9f38"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 673 := ![
  3,
  7,
  301,
  318,
  657,
  660,
  663,
  667,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(24, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(34, 1), (49, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(34, 1), (49, 1), (57, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (64, 1)] }, { coefficient := -1, powers := [(37, 1), (49, 1), (54, 1), (64, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }, { coefficient := 1, powers := [(34, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (57, 1), (69, 1)] }, { coefficient := -1, powers := [(18, 1), (37, 1), (54, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (49, 1), (57, 1), (69, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (49, 1), (54, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (54, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_2_1_7_7.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_2_1_7_7
