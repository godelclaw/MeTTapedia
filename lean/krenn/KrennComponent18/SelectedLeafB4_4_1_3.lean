import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_4_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bfdf89df2a072a819e3be3eb4a6a17c149270b287382a6648166c988910cb2ba"
def certificateSHA256 : String := "a9ac1bff2642fd35d72e0b611f8d88b1ef3ebbf5f639fc4e38fac384532a9c57"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 670 := ![
  148,
  319,
  501,
  505,
  521,
  604,
  605,
  606,
  607,
  656,
  659,
  662,
  665,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(28, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (19, 1), (28, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (36, 1), (39, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (46, 2)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 2)] }, { coefficient := -1, powers := [(22, 1), (46, 1)] }, { coefficient := -2, powers := [(22, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (39, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (31, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (36, 1), (39, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (25, 1), (28, 1), (46, 2)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (25, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (25, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (25, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (28, 1), (31, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (31, 1), (36, 1), (39, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (25, 1), (46, 2)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (31, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (46, 1)] }, { coefficient := 2, powers := [(15, 1), (22, 1), (25, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (31, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (31, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (31, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (28, 1), (31, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (31, 1), (36, 1), (39, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (31, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (31, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (31, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (31, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (28, 1), (46, 2), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (28, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (36, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (36, 1), (39, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (46, 2), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (46, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (28, 1), (46, 3)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (28, 1), (46, 2), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (36, 1), (39, 1), (46, 2)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (36, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (46, 3)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 2)] }, { coefficient := 2, powers := [(11, 1), (22, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 2), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (28, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (28, 1), (46, 2)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (46, 2)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (52, 2)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_4_1_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_4_1_3
