import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_7_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7ad4557a24b056daff759326491d9c86793039c40da80f432d5d4e8168aac950"
def certificateSHA256 : String := "4be117d0953c2ce432f0a68a9caf6c36f1b8c0777bd44f413d532ae586a06431"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 676 := ![
  4,
  50,
  132,
  164,
  176,
  365,
  429,
  455,
  472,
  525,
  585,
  608,
  610,
  611,
  618,
  656,
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
def selectedEquations : Fin 23 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (46, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (57, 2), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (33, 1), (57, 1), (63, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (38, 1), (57, 1), (63, 1), (69, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (57, 2), (69, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (65, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1), (65, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (57, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (57, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (69, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (57, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (24, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (30, 1), (46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (18, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (33, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 2), (38, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(23, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (33, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (33, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (69, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (38, 1), (57, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (18, 1), (24, 1), (42, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (24, 1), (42, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (24, 1), (46, 2), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (24, 1), (46, 2), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (30, 1), (42, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (30, 1), (46, 2), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (33, 1), (46, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (33, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (33, 1), (46, 2), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (33, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (42, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (22, 1), (33, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (33, 2), (38, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(4, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (38, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (22, 1), (33, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (33, 2), (38, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (22, 1), (33, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (33, 2), (38, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (38, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (38, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (39, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (33, 1), (57, 2)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (57, 2)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (27, 1), (33, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (33, 1), (36, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (33, 1), (57, 2)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (41, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (38, 1), (53, 1), (57, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_7_2_1.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_7_2_1
