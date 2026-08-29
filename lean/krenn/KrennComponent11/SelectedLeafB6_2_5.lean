import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a6bbbf39e8e757242f9bbe2adbbb1ba489070f7ee792db4f84d397a69966d33c"
def certificateSHA256 : String := "34fe8b6efc99c22652716285903b15dc4b3df4804ae1901ea3d1f55ee3e087f2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 672 := ![
  11,
  12,
  13,
  19,
  161,
  262,
  269,
  328,
  329,
  330,
  341,
  453,
  488,
  662,
  664,
  665,
  668,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (47, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (45, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (20, 1), (23, 1), (57, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (57, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (49, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 2), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (30, 1), (49, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (36, 1), (39, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_2_5.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_2_5
