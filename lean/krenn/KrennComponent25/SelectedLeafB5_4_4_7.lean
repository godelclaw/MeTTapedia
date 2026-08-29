import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_4_4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c242f6e374d95109f5f86c79628035b08ab0f5b2c90280cc4fdfbe26729ea6bb"
def certificateSHA256 : String := "9fdc2b4114907cf178b399e8920e7a9274cec38830b1e81644493ebd4c32a485"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 668 := ![
  14,
  21,
  162,
  163,
  169,
  170,
  173,
  177,
  293,
  300,
  310,
  312,
  388,
  406,
  430,
  435,
  450,
  461,
  513,
  580,
  655,
  656,
  660,
  661,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (46, 1), (50, 1), (65, 1)] }, { coefficient := 2, powers := [(23, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (50, 1), (65, 1)] }, { coefficient := 2, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (29, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (54, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (48, 1), (54, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (48, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (24, 2), (29, 1), (48, 1), (53, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (24, 1), (29, 1), (48, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 2), (29, 1), (48, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (29, 1), (48, 1), (50, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (19, 1), (29, 1), (50, 1), (65, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (29, 1), (48, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1), (50, 1), (65, 1)] }, { coefficient := -2, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (24, 2), (29, 1), (48, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (29, 1), (48, 1), (54, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (29, 1), (48, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (24, 2), (29, 2), (48, 1), (53, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (24, 1), (29, 2), (48, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 2), (29, 2), (48, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (29, 2), (48, 1), (50, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (19, 1), (29, 1), (50, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (24, 1), (29, 1), (50, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (29, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (24, 1), (29, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 2), (29, 1), (48, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (29, 1), (48, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (22, 1), (29, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (54, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (45, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (24, 2), (29, 1), (45, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (24, 1), (29, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (29, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 2), (29, 1), (45, 1), (48, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (29, 1), (45, 1), (48, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_4_4_7.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_4_4_7
