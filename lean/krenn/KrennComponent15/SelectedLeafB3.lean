import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ceb305249da111a48827276be51bc14f931ad4a861dc93bff7df5e93dda93888"
def certificateSHA256 : String := "095a60912fb217b6ff828875848829e1d37d092047fe4582d434595bacf0d6ef"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 589 := ![
  2,
  3,
  4,
  5,
  9,
  226,
  227,
  234,
  365,
  367,
  368,
  471,
  475,
  476,
  493,
  494,
  519,
  585,
  586,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(8, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (52, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (32, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (26, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (43, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (43, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1), (43, 1), (57, 1)] }, { coefficient := -2, powers := [(16, 1), (21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (29, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (23, 1), (40, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (33, 1), (56, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (40, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (26, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (43, 1), (50, 1)] }, { coefficient := 2, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (43, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (29, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (23, 1), (40, 1), (48, 1)] }]
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
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB3
