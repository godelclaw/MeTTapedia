import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7a17b9eb60dd68c8be234b4db31414f8cae0f91fe57d5f1e487836a60948c617"
def certificateSHA256 : String := "fa0c06fa9bdbaacf719e12ef0c8a47ac1b5164367a67ccc35e17e2adc8c443b8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 673 := ![
  187,
  191,
  193,
  277,
  300,
  301,
  319,
  324,
  382,
  396,
  397,
  422,
  430,
  451,
  452,
  510,
  581,
  623,
  625,
  660,
  663,
  666,
  668,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (49, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (28, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (51, 2), (65, 1)] }, { coefficient := 1, powers := [(51, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (49, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (28, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (47, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (37, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (47, 1), (49, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (47, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (42, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (39, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (44, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (28, 1), (39, 1), (47, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (28, 1), (44, 1), (47, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (28, 1), (45, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (28, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (31, 1), (37, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (34, 1), (37, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (34, 1), (37, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (34, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (22, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (39, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (31, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (42, 1), (49, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (28, 1), (42, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (42, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (51, 2), (65, 1)] }, { coefficient := -1, powers := [(42, 1), (51, 1), (53, 1), (65, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_5_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_5_1
