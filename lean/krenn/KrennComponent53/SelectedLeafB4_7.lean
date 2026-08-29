import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component53.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b4330326af77ab940d6a52d200d569e43fff512b14fe175c7a9fe7f2bcd9aa2c"
def certificateSHA256 : String := "d3079ba127c9d936b9eee1d0fe0806cc849f7dedbcbad7f93e804f9a55ef343a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 643 := ![
  2,
  4,
  5,
  20,
  28,
  162,
  167,
  168,
  208,
  230,
  244,
  347,
  349,
  357,
  359,
  360,
  449,
  559,
  584,
  630,
  636,
  637,
  639,
  641,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (38, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (38, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (34, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (34, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (25, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (43, 1), (47, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (34, 1), (51, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (57, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (48, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(14, 1), (25, 1), (48, 1), (54, 1), (61, 1), (64, 2)] }, { coefficient := -2, powers := [(21, 1), (31, 1), (43, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (34, 1), (61, 1)] }, { coefficient := 2, powers := [(14, 1), (25, 1), (54, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(43, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (34, 1), (57, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (54, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(43, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(26, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(21, 1)] }],
  [{ coefficient := 2, powers := [(14, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(43, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (34, 1), (43, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (48, 1)] }, { coefficient := -2, powers := [(14, 1), (25, 1), (48, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(40, 1), (60, 1)] }, { coefficient := -2, powers := [(42, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(43, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(43, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(43, 1), (57, 1)] }, { coefficient := 2, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -2, powers := [(21, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (26, 1), (34, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (26, 1), (34, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (34, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (34, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (26, 1), (34, 1), (48, 1), (61, 1)] }, { coefficient := 2, powers := [(14, 1), (25, 1), (26, 1), (48, 1), (54, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (31, 1), (43, 1), (47, 1), (63, 1)] }, { coefficient := 2, powers := [(21, 1), (26, 1), (31, 1), (43, 1), (51, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component53.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component53.SelectedLeafB4_7
