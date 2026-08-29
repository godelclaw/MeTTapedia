import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "da0794ff71e08f9ec3a8e863a693dbcf3b79fd28e80dd49fe85627a07a053e7b"
def certificateSHA256 : String := "ac6c668a6b38d134a6cf17bbb8a6c7ec0ccd05291b51b706bf9454bc85c6a73d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 608 := ![
  1,
  2,
  3,
  4,
  5,
  18,
  32,
  311,
  324,
  325,
  434,
  436,
  441,
  456,
  486,
  541,
  550,
  572,
  593,
  601,
  602,
  603,
  604,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (28, 1), (55, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (13, 1), (29, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (29, 1), (44, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (43, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (43, 1), (44, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (43, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (23, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (44, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (23, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (29, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (43, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (43, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (43, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (28, 1), (46, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (29, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (19, 1), (23, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (23, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (25, 1), (32, 1), (43, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (25, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (29, 1), (44, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB2_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB2_4
