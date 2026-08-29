import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB4_2_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "36a649f32c7f8f2a6f68b5af9ae73a3e3d886bed2487c94159d8cfc647901490"
def certificateSHA256 : String := "775b4e258dd4dae2bf70f1e9b990fe81f5c5492582f37141df4055bed378cd88"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 676 := ![
  4,
  164,
  176,
  336,
  365,
  525,
  585,
  608,
  609,
  610,
  611,
  662,
  665,
  670,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(3, 1), (26, 2), (36, 1), (46, 1), (53, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (46, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (46, 1), (57, 1), (68, 1)] }, { coefficient := -2, powers := [(23, 1), (26, 2), (53, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 2), (57, 2), (66, 1), (68, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (57, 2), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (56, 1), (57, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 2), (36, 1), (39, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (39, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (46, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (46, 1), (68, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (68, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (36, 1), (46, 1), (53, 1), (66, 1)] }, { coefficient := -2, powers := [(23, 1), (26, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1), (36, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 2), (36, 1), (46, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (31, 1), (36, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (36, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(22, 1), (31, 1), (46, 1), (68, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 2), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 2), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(23, 1), (26, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (31, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (68, 1)] }, { coefficient := 1, powers := [(26, 2), (36, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (36, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(42, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (36, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (26, 1), (36, 1), (46, 1), (53, 2)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(16, 1), (23, 1), (26, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (26, 1), (36, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (36, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (26, 2), (36, 1), (46, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (26, 1), (36, 1), (46, 1), (53, 2)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (36, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (26, 2), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (26, 2), (57, 2), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 2), (36, 1), (39, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (26, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB4_2_6_7.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB4_2_6_7
