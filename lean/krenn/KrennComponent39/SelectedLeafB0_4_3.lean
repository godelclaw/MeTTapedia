import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3540027cf1c5b63e366b60ea24ce32db2917fa66fdd681e79d8abd2ed5a4c60c"
def certificateSHA256 : String := "bb85e4624cb5535f99bfac523351ac7246a32ab641bbc751b2f57c80f76a9e0a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 670 := ![
  14,
  26,
  29,
  232,
  280,
  304,
  305,
  462,
  478,
  511,
  602,
  603,
  607,
  644,
  659,
  661,
  662,
  665,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (33, 1), (36, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (42, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (36, 1), (42, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (42, 1), (44, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (51, 2), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (44, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (36, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (25, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (25, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (25, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (63, 1)] }, { coefficient := -1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (25, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (25, 1), (45, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (39, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (45, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (25, 1), (44, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (25, 1), (45, 1), (51, 2), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1), (44, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1), (51, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (44, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := 1, powers := [(44, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (23, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (51, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_4_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_4_3
