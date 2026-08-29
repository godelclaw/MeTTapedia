import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a592c731fb7b1f10193180098bf6ad687f092d2023861b911a0ba3c232fd1bb7"
def certificateSHA256 : String := "48fc45ee6cb4924a3c3018613ef4c3ef9e2fb9daf982676c596f282cb7d97fc4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 668 := ![
  22,
  25,
  86,
  145,
  164,
  168,
  169,
  172,
  177,
  178,
  179,
  273,
  293,
  294,
  301,
  302,
  308,
  316,
  434,
  443,
  462,
  463,
  467,
  506,
  517,
  556,
  578,
  655,
  658,
  661,
  662,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(8, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (40, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (51, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (24, 1), (46, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (43, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 2), (29, 1), (48, 1), (51, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 2), (29, 1), (48, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (29, 1), (48, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (25, 1), (29, 1), (51, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (25, 1), (29, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (29, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (54, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (29, 1), (48, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (29, 1), (48, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (48, 1), (56, 1), (65, 1)] }, { coefficient := -2, powers := [(29, 1), (48, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (51, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1), (54, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (29, 1), (48, 1), (50, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (48, 1), (50, 1), (56, 1), (65, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (25, 1), (29, 1), (40, 1), (43, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (29, 1), (43, 1), (51, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (29, 1), (48, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (29, 1), (51, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (56, 1)] }, { coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (25, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (29, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (56, 1), (65, 1)] }, { coefficient := 2, powers := [(29, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (48, 1), (52, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 2), (29, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 2), (29, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (29, 1), (56, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (29, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (29, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (29, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (24, 1), (46, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (43, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 2), (29, 1), (48, 1), (50, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 2), (29, 1), (48, 1), (50, 1), (56, 1), (65, 1)] }, { coefficient := 2, powers := [(18, 1), (25, 1), (29, 1), (48, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (25, 1), (29, 1), (50, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (25, 1), (29, 1), (50, 1), (56, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (29, 1), (50, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_6_7.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_6_7
