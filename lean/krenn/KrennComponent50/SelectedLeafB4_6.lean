import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component50.SelectedLeafB4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cddd81288bab0101e75dd2ec35ef20cce0e43759113a29fa5636a7eb1a4ddf54"
def certificateSHA256 : String := "a347e4173412585ad2bf99084a400bee651d4cc19c357982430359eb0f14918d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 641 := ![
  2,
  3,
  14,
  25,
  26,
  162,
  164,
  228,
  243,
  348,
  349,
  362,
  363,
  367,
  394,
  634,
  635,
  637,
  638,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 2), (30, 1), (33, 1), (40, 1), (56, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 2), (30, 1), (31, 1), (33, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (8, 1), (24, 1), (33, 1), (40, 1), (56, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (33, 1), (40, 1), (47, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (40, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (9, 1), (33, 2), (56, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 2), (9, 1), (33, 1), (36, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 2), (33, 1), (36, 1), (40, 1), (53, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (33, 2), (40, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 2), (33, 1), (40, 1), (56, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (8, 1), (33, 1), (40, 1), (56, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (40, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (40, 1), (47, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (19, 1), (33, 1), (40, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (14, 1), (33, 1), (40, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (33, 2), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 2), (33, 1), (36, 1), (53, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (31, 1), (33, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (40, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (40, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (39, 1), (40, 1), (56, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (40, 1), (47, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (40, 1), (47, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (40, 1), (47, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (33, 1), (40, 1), (56, 2), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (8, 1), (33, 1), (36, 1), (40, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (60, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component50.SelectedLeafB4_6.selectedHasNoCommonZero

end Krenn.Component50.SelectedLeafB4_6
