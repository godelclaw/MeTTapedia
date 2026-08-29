import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB2_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9530dcdddfaaa773132d68c25c21dc1a671839ebead28c5c68bf4df0c4aee44d"
def certificateSHA256 : String := "bd2d653b88260f3c2023f0c5caf4586a6d212d546fb7f55f9c7358c82a07de40"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 667 := ![
  0,
  1,
  3,
  4,
  181,
  294,
  313,
  440,
  447,
  454,
  458,
  465,
  466,
  472,
  474,
  503,
  529,
  566,
  581,
  628,
  638,
  645,
  657,
  658,
  659,
  660,
  663,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (44, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (44, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (33, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (24, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (36, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(41, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(46, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (41, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (44, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := 1, powers := [(46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (44, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (46, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (24, 1), (44, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (44, 1), (48, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (44, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (41, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (46, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (52, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (49, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (41, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB2_2_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB2_2_3
