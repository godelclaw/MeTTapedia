import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_6_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "164e594fd7727bc4ee2c0a6d7d80bd5c52b05a902a63e040d8761130c0f58185"
def certificateSHA256 : String := "9648d23d5c29fe9755c95b7e8f6060d58a84118b67cf3835d1be0a6e04d4515e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 675 := ![
  6,
  11,
  12,
  169,
  180,
  326,
  328,
  329,
  330,
  341,
  375,
  453,
  589,
  662,
  664,
  665,
  668,
  670,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (28, 1)] }, { coefficient := -1, powers := [(22, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (39, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (53, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(69, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (69, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (49, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (30, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (69, 1)] }, { coefficient := -1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (36, 1), (39, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_6_5_7.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_6_5_7
