import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2df26b33bbc1188450ff7ec208a122cedc8a63faf90854a2710a00d10f5d996d"
def certificateSHA256 : String := "be0879a00d3b442f50704fbb81d7715cbfb46c53ca6780a59fc005f8996f098f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 608 := ![
  1,
  2,
  3,
  4,
  7,
  30,
  185,
  210,
  300,
  311,
  325,
  338,
  378,
  397,
  534,
  541,
  572,
  601,
  602,
  603,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (43, 1), (59, 2)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (21, 1), (24, 1), (32, 1), (59, 2)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (24, 1), (32, 1), (43, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (24, 1), (32, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (25, 1), (32, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (24, 1), (32, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (45, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (43, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (21, 1), (24, 1), (32, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (32, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (25, 1), (32, 1), (43, 1), (59, 1)] }],
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB3_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB3_4
