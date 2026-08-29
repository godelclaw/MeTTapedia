import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component50.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a55eba4650f54da7380d6ba98eca2496f8c8b829d01d4c1929f7912f03bda1ce"
def certificateSHA256 : String := "5a96844c7a419da96f4f9cca62a81039fbf1f8c2a0abccf42ba9c62e6435543c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 638 := ![
  2,
  3,
  40,
  206,
  207,
  209,
  211,
  216,
  228,
  243,
  362,
  363,
  477,
  478,
  634,
  635,
  636,
  637
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (42, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (36, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (39, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (39, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component50.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component50.SelectedLeafB3
