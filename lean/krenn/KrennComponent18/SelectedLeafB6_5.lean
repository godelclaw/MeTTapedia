import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4276b2c1d6f65f97ada00aab7a87ac1e9c25d197f07b585e18a4045f2fdc346d"
def certificateSHA256 : String := "3d04d3ed3c31d964cd3e02245cde0b6ad6549bbd398edac368822f59ea6ab844"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 664 := ![
  10,
  19,
  20,
  25,
  167,
  168,
  295,
  301,
  304,
  318,
  327,
  409,
  424,
  433,
  437,
  443,
  463,
  562,
  609,
  652,
  657,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (47, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (31, 1), (43, 1), (47, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (26, 1), (43, 1), (47, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (43, 1), (47, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (47, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (47, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (43, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (31, 1), (43, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (48, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (43, 1), (63, 1)] }, { coefficient := -2, powers := [(24, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (26, 1), (43, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (26, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(26, 1), (43, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(43, 1), (57, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (34, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (25, 1), (31, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (26, 1), (43, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (25, 1), (43, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (25, 1), (26, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (34, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (34, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (25, 1), (31, 1), (43, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (25, 1), (26, 1), (43, 1), (47, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (43, 1), (47, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (43, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (25, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (31, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (25, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (31, 1), (43, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_5
