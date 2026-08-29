import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_6_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9887b0d046d37e7899eafb7abd8c3380a98a5b92a4f61f7ee68320347d5eb6ef"
def certificateSHA256 : String := "dd21d4fae4bb3956aca8fa5e669dc1c0c247297f92a353723188e91aab00ea0e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 670 := ![
  294,
  304,
  323,
  424,
  451,
  457,
  463,
  498,
  499,
  565,
  661,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (42, 1), (51, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (30, 1), (51, 1), (53, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (51, 1), (52, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(26, 1), (41, 1), (42, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (51, 1), (52, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (51, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (42, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (51, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (52, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (30, 1), (53, 1), (63, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (41, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1), (63, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (51, 1), (63, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (51, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (47, 1), (51, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (45, 1), (51, 1), (53, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (45, 1), (51, 1), (52, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(26, 1), (41, 1), (47, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (51, 1), (52, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (63, 1)] }, { coefficient := -1, powers := [(41, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_6_3_1.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_6_3_1
