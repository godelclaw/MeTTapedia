import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB4_5_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c95fc3ff7c6c1eb240d5fceed271b6b93c2f34888936878cde0e5c874caf41ae"
def certificateSHA256 : String := "828b129a343ab78076ae89e00de0153258046fd5436de7d0ba68e20770388c8c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 671 := ![
  18,
  19,
  24,
  26,
  29,
  172,
  260,
  278,
  309,
  310,
  420,
  421,
  423,
  540,
  558,
  661,
  664,
  665,
  666,
  667,
  668,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(28, 1), (40, 1), (43, 1), (47, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (45, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (40, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (40, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (40, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (40, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (40, 1), (47, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1), (40, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (40, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (40, 2), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (47, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (40, 1), (42, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(38, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(40, 2), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (47, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (28, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (40, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (28, 1), (40, 2), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(13, 1), (28, 1), (40, 1), (47, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (40, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB4_5_6.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB4_5_6
