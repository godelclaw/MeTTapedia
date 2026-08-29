import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f0df3986d66d40e3fc551aba4670d71e9c8ac7968388da6a19f73294db35423f"
def certificateSHA256 : String := "fbee92358822ab16de73fd286db46cb2b89a3d1c096a97b1549806424d663488"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 667 := ![
  1,
  4,
  6,
  7,
  8,
  9,
  33,
  184,
  193,
  225,
  285,
  309,
  318,
  430,
  434,
  440,
  510,
  566,
  570,
  650,
  655,
  660,
  662,
  663,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (50, 1), (62, 1), (63, 1)] }, { coefficient := 2, powers := [(11, 1), (21, 1), (40, 1), (53, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (50, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1), (44, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (11, 1), (34, 1), (40, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (27, 1), (40, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (27, 1), (40, 1), (62, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (40, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (17, 1), (40, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (40, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(3, 1), (11, 1), (34, 1), (40, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 2, powers := [(9, 1), (17, 1), (27, 1), (40, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(11, 1), (21, 1), (40, 1), (42, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (40, 1), (42, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (27, 1), (40, 1), (50, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (40, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (40, 1), (42, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -2, powers := [(38, 1), (40, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (40, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(40, 1), (45, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (31, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (22, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (28, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB6_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB6_7
