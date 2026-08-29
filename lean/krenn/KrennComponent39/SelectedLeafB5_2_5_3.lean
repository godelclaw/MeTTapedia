import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "60bed36538953f733f82407cb8a9651931320928744e83c567a0f013804262f0"
def certificateSHA256 : String := "2bdb4a9b5d7665c0c9e2d3720f650bc2c7558e2102c7fa6f031e9cdd57b6af22"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 673 := ![
  22,
  29,
  300,
  410,
  416,
  422,
  439,
  441,
  452,
  462,
  482,
  580,
  604,
  607,
  644,
  649,
  663,
  668,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(0, 2), (21, 1), (36, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 2), (26, 1), (35, 1), (51, 2), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 2), (26, 1), (36, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 2), (27, 1), (35, 1), (51, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (26, 1), (51, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (27, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (39, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (35, 1), (51, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (39, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (35, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (24, 1), (36, 1), (44, 1), (59, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (44, 1), (53, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (35, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (26, 1), (35, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (16, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (44, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (35, 1), (51, 1), (59, 2)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (35, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (26, 1), (35, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (35, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (21, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (35, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (42, 1), (44, 1), (53, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (39, 1), (42, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (16, 1), (21, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (26, 1), (35, 1), (51, 2), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (26, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (16, 1), (27, 1), (35, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (24, 1), (36, 1), (42, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (26, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (16, 1), (27, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (26, 1), (35, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (35, 1), (59, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_5_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_5_3
