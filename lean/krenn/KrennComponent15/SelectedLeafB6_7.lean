import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c0b88ab9063e6b58762cd0d7b39dd8eb79cf27b8817eb128a6456eb17d5762d7"
def certificateSHA256 : String := "b7de66bf8f622e872f873fd2925e1ee6a0470c4772d89f7e78bc18ed8543f791"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 592 := ![
  0,
  1,
  2,
  4,
  5,
  13,
  17,
  29,
  226,
  227,
  335,
  350,
  365,
  366,
  400,
  413,
  429,
  471,
  519,
  585,
  587,
  588,
  589,
  590
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(1, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (29, 1), (47, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (38, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (36, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (53, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (38, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB6_7.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB6_7
