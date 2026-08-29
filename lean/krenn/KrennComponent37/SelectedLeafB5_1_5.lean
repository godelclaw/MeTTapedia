import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2a1e60e608c6b676a480d933c3adcd36bd92ec0db125d0102c08346013f445be"
def certificateSHA256 : String := "9ab9ccaf24d3af5b46bd735a3508a14eea31e2f0238ab7f1d42cbe8131e892b0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 667 := ![
  13,
  17,
  23,
  27,
  149,
  152,
  182,
  221,
  283,
  298,
  299,
  300,
  301,
  313,
  427,
  466,
  484,
  581,
  583,
  584,
  591,
  602,
  603,
  604,
  655,
  656,
  659,
  660,
  661,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (13, 1), (31, 1), (37, 1), (44, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1), (43, 1), (44, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (37, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (37, 1), (43, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (31, 1), (37, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (43, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (31, 1), (37, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1), (43, 1), (51, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (47, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (13, 1), (31, 1), (37, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1), (43, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (31, 1), (37, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1), (43, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (31, 1), (37, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1), (43, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (37, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (37, 1), (43, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (26, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (44, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (38, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (44, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(27, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (47, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (13, 1), (31, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (31, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (35, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (13, 1), (27, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (31, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (27, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (31, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (27, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (31, 1), (37, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (31, 1), (32, 1), (37, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (26, 1), (44, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 2), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (22, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (27, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (22, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (31, 1), (37, 1), (43, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_1_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_1_5
