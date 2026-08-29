import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4ffd5282b69a905d20e04afc0b2ee71c6c9efcf250edfa79f77c87a1eb647afc"
def certificateSHA256 : String := "913793f205eee696b65beaa3a064cfaf51109379895956abed53e3a4c15fb8d2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 667 := ![
  1,
  2,
  3,
  4,
  148,
  149,
  181,
  222,
  294,
  301,
  313,
  318,
  358,
  427,
  454,
  466,
  566,
  581,
  583,
  602,
  603,
  655,
  657,
  659,
  660,
  661,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (13, 1), (31, 1), (33, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (44, 1), (59, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (44, 1), (59, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (44, 1), (59, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (24, 1), (31, 1), (37, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (31, 1), (37, 1), (43, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (31, 1), (37, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (31, 1), (37, 1), (43, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (31, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (36, 1), (37, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (37, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (37, 1), (49, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (43, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (37, 1), (48, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (33, 1), (37, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (37, 1), (43, 1), (48, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (37, 1), (43, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (31, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (43, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (30, 1), (37, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (37, 1), (43, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (54, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (26, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (37, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (37, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 1), (43, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (44, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (44, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (44, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (31, 1), (36, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (44, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (44, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (31, 1), (33, 1), (37, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (24, 1), (31, 1), (37, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (31, 1), (37, 1), (43, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (31, 1), (37, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (31, 1), (37, 1), (43, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (39, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (30, 1), (37, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (33, 1), (37, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (30, 1), (37, 1), (48, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (33, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (30, 1), (37, 1), (43, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (33, 1), (37, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (30, 1), (37, 1), (43, 1), (48, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (33, 1), (37, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (31, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (31, 1), (36, 1), (37, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (26, 1), (44, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (30, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_2_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_2_1
