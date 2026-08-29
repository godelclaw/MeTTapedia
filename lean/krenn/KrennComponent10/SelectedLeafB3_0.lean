import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "99a84ef8d216f6d36fb4fe300e4cba109c212c4820570429a545f461051d92be"
def certificateSHA256 : String := "da60d9afc88921d1d75efe77d63ee3e923f9723d86facc32b67219134e13ba16"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 641 := ![
  2,
  20,
  29,
  31,
  37,
  189,
  196,
  197,
  200,
  202,
  348,
  349,
  359,
  409,
  473,
  550,
  576,
  577,
  586,
  632,
  634,
  635,
  636,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (19, 1), (22, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 2), (22, 1), (38, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (22, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (22, 1), (38, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (22, 1), (24, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (19, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 2), (38, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (45, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (24, 1), (38, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (19, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 2), (38, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (42, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (33, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (17, 1), (19, 1), (27, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (24, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (19, 2), (27, 1), (38, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (19, 1), (27, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (19, 1), (27, 1), (38, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (24, 1), (27, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB3_0.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB3_0
