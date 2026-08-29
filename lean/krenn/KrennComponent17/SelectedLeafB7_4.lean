import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3fa4f8510160fdf7406e82e240b43c910db69c32195315cdffcb8c801b4a0346"
def certificateSHA256 : String := "eb498047da1cc189ba1f16cf6c4602c681fbe10c4aff28b02566415acc4c55f4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 608 := ![
  2,
  3,
  4,
  18,
  32,
  183,
  206,
  207,
  311,
  323,
  325,
  415,
  423,
  428,
  434,
  441,
  507,
  541,
  552,
  572,
  601,
  602,
  603,
  604,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (28, 1), (32, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (28, 1), (45, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (28, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (28, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (25, 1), (28, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (25, 1), (28, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (28, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (28, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (25, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (23, 1), (25, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (43, 1), (51, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (17, 1), (25, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (25, 1), (27, 1), (32, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (19, 1), (25, 1), (28, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (24, 1), (25, 1), (28, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (25, 1), (27, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (17, 1), (23, 1), (25, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (23, 1), (25, 1), (27, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (19, 1), (23, 1), (25, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (23, 1), (24, 1), (25, 1), (28, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (23, 1), (25, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB7_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB7_4
