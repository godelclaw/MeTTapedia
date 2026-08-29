import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB4_6_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "185d58628cd9ead5909eb87014e959f602d34fe55d73c1fa5ba035105e8abaaa"
def certificateSHA256 : String := "6aaff9c453a1e975a8108bf8c4b2d7c7c2399c68644811efeefaab8341ccf660"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 676 := ![
  4,
  50,
  132,
  164,
  336,
  365,
  525,
  608,
  609,
  610,
  611,
  662,
  665,
  667,
  670,
  673,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 69) := ![
  [{ coefficient := -2, powers := [(23, 1), (26, 2), (53, 1), (57, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 2), (57, 2), (67, 1), (68, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (57, 2), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (56, 1), (57, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 2), (36, 1), (39, 1), (57, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (39, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (46, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1), (68, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (68, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (26, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (31, 1), (46, 1), (68, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 2), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 2), (57, 1), (67, 1)] }, { coefficient := -2, powers := [(23, 1), (26, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (31, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (68, 1)] }, { coefficient := 1, powers := [(26, 2), (36, 1), (39, 1), (67, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (36, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(42, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (23, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(16, 1), (23, 1), (26, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (26, 2), (53, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (26, 2), (57, 2), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 2), (36, 1), (39, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (26, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (53, 2)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB4_6_6_5.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB4_6_6_5
