import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_2_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "511e4856294070ce4b00974ad8f043cfe048690532df80a0fe529f26c0d6e978"
def certificateSHA256 : String := "585c0acbf467dde003a9b3e1f064054adbdc38ab08e515c34451406bd0ede6a4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 670 := ![
  171,
  179,
  180,
  181,
  294,
  311,
  312,
  313,
  393,
  410,
  411,
  433,
  438,
  450,
  454,
  466,
  566,
  570,
  650,
  657,
  660,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (52, 2), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (52, 1), (54, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (44, 1), (48, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (26, 1), (52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (58, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (48, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (53, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(24, 1), (55, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (48, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 2), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (24, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (52, 2), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (44, 1), (52, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (24, 1), (41, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (24, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (41, 1), (48, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (46, 1), (48, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (47, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (41, 1), (44, 1), (55, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (41, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (46, 1), (55, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (46, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (47, 1), (55, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (41, 1), (55, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (44, 1), (46, 1), (48, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (47, 1), (48, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1), (58, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_2_3_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_2_3_0
