import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_0_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6cb1398d40282da916f7b03d36bfcd6d84b71274ef7228aa85d930f0e059d453"
def certificateSHA256 : String := "6a7c0d487b1b3c7d999ea1644bf2ff753672ccaed7d6d530a2f71d06a0a09157"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 670 := ![
  15,
  17,
  25,
  150,
  300,
  301,
  302,
  487,
  591,
  602,
  603,
  612,
  647,
  655,
  660,
  661,
  662,
  664,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (23, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (28, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (37, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (37, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (28, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (25, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (28, 1), (59, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (23, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (25, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (23, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (28, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (37, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (28, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (25, 1), (28, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (25, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (45, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (27, 1), (28, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (18, 1), (28, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (27, 1), (28, 1), (37, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (25, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (27, 1), (28, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (25, 1), (27, 1), (28, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (25, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (20, 1), (28, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (25, 1), (28, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 2), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (37, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1)] }, { coefficient := -2, powers := [(20, 1), (50, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (9, 1), (17, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (23, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (28, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (28, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (17, 1), (20, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (17, 1), (25, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (23, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (23, 1), (25, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (25, 1), (28, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_0_2_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_0_2_7
