import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_7_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0bc6b01eab7026ba0cbd0e7e27f17e520263f70e4eff0d45b0ac7363bb243e5d"
def certificateSHA256 : String := "a5834525e65baa04a3e40b4588c892af92fd61373f5f3e8c397dc41705c8ba16"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 676 := ![
  4,
  23,
  164,
  176,
  365,
  447,
  472,
  525,
  583,
  585,
  608,
  609,
  610,
  611,
  652,
  655,
  656,
  662,
  664,
  665,
  666,
  669,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (48, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 71) := ![
  [{ coefficient := -2, powers := [(23, 1), (26, 2), (53, 1), (57, 1), (68, 1), (70, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 2), (57, 2), (68, 1), (70, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 1), (53, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (57, 2), (70, 1)] }, { coefficient := -1, powers := [(26, 2), (36, 1), (39, 1), (57, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (39, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(28, 1), (46, 1), (70, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (46, 1), (51, 1), (57, 1), (66, 1), (70, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (46, 1), (54, 1), (66, 1), (70, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (46, 1), (51, 1), (66, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (4, 1), (33, 1), (57, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (20, 1), (33, 1), (57, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (33, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (20, 1), (33, 1), (57, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (70, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1), (70, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 1), (53, 1), (70, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(23, 1), (70, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (39, 1), (70, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1), (70, 1)] }, { coefficient := 1, powers := [(28, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (48, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (18, 1), (33, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (20, 1), (33, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (26, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (33, 1), (62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (31, 1), (46, 1), (70, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 2), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 2), (57, 1), (68, 1)] }, { coefficient := -2, powers := [(23, 1), (26, 1), (31, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (31, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (70, 1)] }, { coefficient := 1, powers := [(26, 2), (36, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (36, 1), (39, 1), (70, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (70, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (33, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (23, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(16, 1), (23, 1), (26, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (4, 1), (33, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (4, 1), (33, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (20, 1), (33, 1), (42, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (20, 1), (33, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (20, 1), (33, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (20, 1), (33, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (26, 2), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (26, 2), (57, 2), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 2), (36, 1), (39, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (46, 1), (48, 1), (51, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (46, 1), (48, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (26, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1), (48, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (53, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_7_2_7.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_7_2_7
