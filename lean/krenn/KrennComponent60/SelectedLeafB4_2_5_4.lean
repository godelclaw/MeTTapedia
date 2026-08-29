import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_5_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "add0fa96147d6f658c469daed75815cc005530d543b0c936a17f06f860d3f39f"
def certificateSHA256 : String := "d4c7e8e64bc99ebb509f4e24c1793e3011b48046e10513a2463a4496a800fa5f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 668 := ![
  22,
  143,
  169,
  172,
  177,
  178,
  236,
  294,
  301,
  302,
  308,
  310,
  327,
  383,
  404,
  443,
  556,
  579,
  599,
  621,
  655,
  656,
  658,
  661,
  662,
  663,
  664,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(12, 1), (53, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (50, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (57, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (25, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(50, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (57, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (50, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (38, 1), (57, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (47, 1), (53, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(47, 1), (50, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 2), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (20, 1), (24, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (24, 1), (25, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (57, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1), (50, 1), (57, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_5_4.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_5_4
