import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_6_5_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0da020748da7e0b79c0ca3d7fe7ae4dd0d6a2b212352153b7ef53c434b3b6cda"
def certificateSHA256 : String := "949d46cfc16d0753a0f45f7919ed9ccb2ac301a5ee8f388095b10acb7f6316ce"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 673 := ![
  6,
  167,
  175,
  179,
  438,
  454,
  621,
  623,
  642,
  657,
  663,
  666,
  667,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(36, 1), (55, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1)] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_6_5_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_6_5_6
