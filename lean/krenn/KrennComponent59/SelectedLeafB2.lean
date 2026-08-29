import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2e277e4dca7a92b1afd28e98396d47cbc0c8b0cd93f347b42d2cfcf22a2f71c8"
def certificateSHA256 : String := "a8b87277e409b86deb7ac673c86fb242af3d8233f6a7f088f973f536d2ed0d98"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 614 := ![
  9,
  15,
  19,
  20,
  35,
  195,
  196,
  197,
  217,
  220,
  222,
  224,
  338,
  341,
  349,
  461,
  471,
  489,
  559,
  583,
  610,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 59) := ![
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (20, 1), (32, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (32, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (26, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (20, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (32, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (32, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (45, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(35, 1), (57, 1)] }, { coefficient := 1, powers := [(38, 1), (54, 1)] }]
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
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component59.SelectedLeafB2.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB2
