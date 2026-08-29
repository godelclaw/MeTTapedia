import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "69971517bc8f3ee7c9b4cd8925c712acc9574a8b1b351d3263bcfb6f3e7b5a7e"
def certificateSHA256 : String := "01538e0ad5ddb911e4bb5ef9c311c2a1ef017fc02f6a8d31961952a846f511e7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 592 := ![
  1,
  2,
  3,
  4,
  5,
  11,
  13,
  17,
  21,
  46,
  128,
  226,
  227,
  268,
  318,
  365,
  366,
  367,
  374,
  382,
  400,
  413,
  429,
  469,
  471,
  519,
  539,
  543,
  544,
  562,
  583,
  585,
  587,
  588,
  589,
  590
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (27, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (33, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (45, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (33, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(36, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (20, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (25, 1), (53, 1), (54, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (29, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (29, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(22, 1), (29, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (33, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (26, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (17, 1), (21, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (41, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (17, 1), (25, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (29, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (29, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (17, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 2, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (29, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (39, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (17, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (39, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (33, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (39, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (20, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (25, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (29, 1), (33, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (29, 1), (39, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (29, 1), (33, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (29, 1), (39, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (17, 1), (18, 1), (41, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (38, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (41, 1), (45, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1), (45, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (53, 1)] }, { coefficient := -2, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (29, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (17, 1), (29, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (22, 1), (29, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (29, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (22, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (29, 1), (39, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (38, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB6_3
