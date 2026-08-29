import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_7_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d39d4a9a8208e9e36efd505a9c51a587faef484833b3fbe73a21e7a1e8dfdc4f"
def certificateSHA256 : String := "5e7e5db7f21dd715a42d3e7ce6c18032027de3474624ca965f2814e2bdfef83b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 676 := ![
  4,
  50,
  132,
  164,
  176,
  365,
  429,
  503,
  525,
  585,
  608,
  610,
  611,
  662,
  665,
  666,
  667,
  673,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (46, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (57, 2), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (53, 1), (57, 1), (68, 2)] }, { coefficient := -1, powers := [(27, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (57, 2), (68, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (57, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (57, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (33, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (33, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (33, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (33, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (53, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (68, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (38, 1), (57, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(31, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := 1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (33, 1), (46, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (33, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (33, 1), (46, 2), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (33, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (42, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (31, 1), (53, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (38, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (24, 1), (33, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (24, 1), (33, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (29, 1), (33, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (29, 1), (33, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (31, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (38, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (31, 1), (42, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (38, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (39, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (33, 1), (57, 2)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (57, 2)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (33, 1), (57, 2)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (41, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (31, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (38, 1), (53, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_7_2_1.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_7_2_1
