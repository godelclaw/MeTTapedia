import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_0_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4c182896d64f21cd61fe23f9f7b7e4958dc6e9b295e2b6368050eab5bae72308"
def certificateSHA256 : String := "c10791272f7c37fad3396857f7ef24b29f92b4bebb80282993b9dae4376ee42e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 648 := ![
  9,
  11,
  27,
  177,
  183,
  194,
  315,
  346,
  347,
  348,
  349,
  352,
  353,
  367,
  534,
  580,
  634,
  635,
  636,
  637,
  638,
  640,
  641,
  644,
  645,
  646,
  647
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (45, 1), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (37, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (32, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (38, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (35, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (35, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (45, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (11, 1), (32, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (37, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (45, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (8, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (29, 1), (35, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (27, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (27, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (32, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (32, 1), (45, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (45, 1), (53, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_0_2_5.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_0_2_5
