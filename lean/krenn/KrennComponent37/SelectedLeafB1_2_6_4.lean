import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_2_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b8bf9e18dd5b1b8d647e36aee3f32fb513528ce02058310dec5812deac5df020"
def certificateSHA256 : String := "ba54ef2800cbb36d53a0455ee4354bfc0b75827e87374f37184572d764152bc8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 670 := ![
  167,
  168,
  170,
  171,
  175,
  176,
  179,
  181,
  183,
  279,
  294,
  296,
  297,
  310,
  313,
  340,
  410,
  411,
  429,
  438,
  440,
  450,
  453,
  458,
  476,
  487,
  499,
  562,
  580,
  581,
  617,
  628,
  657,
  658,
  660,
  663,
  666,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(28, 1), (39, 1), (47, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (37, 1), (47, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (28, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (39, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(28, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (28, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (37, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(29, 1), (39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (51, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (37, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (55, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (28, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (28, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (37, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (28, 1), (38, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (28, 1), (39, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (37, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (28, 1), (33, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (23, 1), (28, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (37, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (28, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (28, 1), (44, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (28, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (37, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (37, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (37, 1), (48, 1), (51, 1), (60, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_2_6_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_2_6_4
