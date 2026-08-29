import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component53.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "813f3aba85b1eb3396d775e1422e9c99a3abc5eb5b47fd0f60f0e944c18e7a5d"
def certificateSHA256 : String := "08ec9170bee8ce3bc0a9c064135251a39f289289753c72c7091bde3a0d3106d9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 643 := ![
  2,
  5,
  22,
  28,
  29,
  161,
  162,
  230,
  244,
  333,
  347,
  349,
  359,
  360,
  386,
  477,
  636,
  637,
  639,
  640,
  641,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (43, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (43, 1), (54, 1), (59, 1), (63, 2)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (43, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (43, 1), (47, 1), (53, 1), (63, 2)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (43, 1), (48, 1), (61, 1), (63, 2)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (43, 1), (48, 1), (54, 1), (61, 1), (63, 3)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (43, 1), (47, 1), (63, 2)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (43, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (43, 1), (54, 1), (61, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (54, 1), (60, 1), (63, 2)] }, { coefficient := 1, powers := [(8, 1), (43, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(43, 2), (54, 1), (63, 2)] }],
  [{ coefficient := -1, powers := [(25, 1), (43, 1), (54, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (43, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (43, 1), (48, 1), (54, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(41, 1), (43, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(43, 2), (48, 1), (54, 1), (63, 2)] }, { coefficient := 1, powers := [(43, 2), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (43, 1), (47, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (43, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (43, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (34, 1), (43, 1), (48, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (26, 1), (43, 1), (48, 1), (54, 1), (61, 1), (63, 2)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component53.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component53.SelectedLeafB4_5
