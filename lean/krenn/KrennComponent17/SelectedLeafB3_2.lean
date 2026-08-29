import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB3_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "546deb4262a543bc478af84c833fa7e4ba72bcee3b5f1b4998aadd6a01c7c263"
def certificateSHA256 : String := "1936557234742278da2e58def2d26a90735365ecce742204b23325d1073413d3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 608 := ![
  1,
  2,
  3,
  4,
  7,
  206,
  210,
  306,
  311,
  325,
  338,
  378,
  410,
  432,
  445,
  454,
  459,
  481,
  506,
  541,
  549,
  550,
  572,
  601,
  602,
  603,
  604,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (28, 1), (32, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (28, 1), (32, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (32, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (32, 1), (44, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (28, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 2), (28, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (22, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (27, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (19, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (19, 1), (28, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (22, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (27, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (32, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (19, 1), (28, 1), (32, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (22, 1), (32, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (27, 1), (32, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB3_2.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB3_2
