import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_2_7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4498ebee88142aef25c605b16e3799edde386b45a8c05de851934dab02b07ea7"
def certificateSHA256 : String := "d8a8a80195e6ce5c275aa90445969d6949782de61d740fe3041c09b9aeb710f0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 673 := ![
  187,
  300,
  319,
  396,
  416,
  422,
  439,
  441,
  458,
  462,
  505,
  532,
  580,
  581,
  607,
  644,
  661,
  663,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (27, 1), (45, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (27, 1), (45, 1), (56, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (44, 1), (51, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (51, 1), (56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (44, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (27, 1), (45, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (45, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 2), (24, 1), (27, 1), (45, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (27, 1), (42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (24, 1), (42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (24, 1), (45, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (24, 1), (42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (24, 1), (27, 1), (45, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (42, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (42, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (24, 1), (27, 1), (45, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (27, 1), (42, 1), (44, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (36, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (36, 1), (42, 1), (59, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (39, 1), (42, 1), (51, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (39, 1), (42, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (42, 1), (44, 1), (51, 2), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (42, 1), (44, 1), (51, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (45, 1), (51, 2), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (45, 1), (51, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(39, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(45, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (45, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (44, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (42, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (42, 1), (51, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_2_7_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_2_7_5
