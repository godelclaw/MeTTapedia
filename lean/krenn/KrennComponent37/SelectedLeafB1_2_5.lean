import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a2da029477c888b84dea027e740dc7a6fc1a0c0372cbeb7eaf0bd3b9e3cabc47"
def certificateSHA256 : String := "5ed4391ff23b43c774274d73b6a1bb491018ec5d62e5dc77801970e8e76d1d04"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 667 := ![
  17,
  149,
  152,
  221,
  300,
  301,
  313,
  427,
  466,
  581,
  583,
  584,
  602,
  603,
  655,
  658,
  660,
  661,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(20, 1), (23, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (20, 1), (37, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (43, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (37, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (26, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (31, 1), (37, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (37, 1), (43, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (44, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (26, 1), (31, 1), (37, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (37, 1), (43, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (43, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (26, 1), (37, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (37, 1), (43, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (47, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (26, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 2), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (26, 1), (31, 1), (37, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (31, 1), (37, 1), (43, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (37, 1), (43, 1), (52, 1)] }]
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

#print axioms Krenn.Component37.SelectedLeafB1_2_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_2_5
