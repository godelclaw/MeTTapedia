import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e7edadb1560e0ce9acc1f9b74cf41bbcc0cf6bfebdac01066279a82d254daeb1"
def certificateSHA256 : String := "0e0208608757e2e14dd125e0121bab2a5b99af560b3144a982a27ee000629429"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 667 := ![
  1,
  2,
  4,
  6,
  7,
  8,
  9,
  184,
  193,
  309,
  397,
  430,
  434,
  440,
  566,
  607,
  655,
  660,
  662,
  663,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (40, 1), (53, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1), (40, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (16, 1), (23, 1), (28, 1), (40, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (24, 1), (40, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (28, 1), (40, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (21, 1), (40, 1), (45, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (21, 1), (40, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (23, 1), (28, 1), (40, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (24, 1), (40, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (40, 1), (42, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (40, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (28, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (40, 1), (42, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(38, 1), (40, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (21, 1), (40, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (23, 1), (28, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (24, 1), (40, 1), (42, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (28, 1), (40, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB6_5
