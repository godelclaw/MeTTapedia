import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component56.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ab6dbfbffffa4712f4c642a87dc6562d183da1f07a25de32995cf7592c88e451"
def certificateSHA256 : String := "2a1bbb07f2e6e6ef206bdf5733a54ec9bbc055af7c3a13d735452681a4944f6f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 589 := ![
  2,
  6,
  9,
  11,
  26,
  212,
  254,
  263,
  274,
  360,
  362,
  372,
  373,
  377,
  379,
  382,
  397,
  585,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (17, 1), (32, 1), (33, 1), (50, 1), (55, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (17, 1), (32, 1), (35, 1), (50, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (22, 1), (33, 1), (44, 1), (50, 1), (55, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 2), (22, 1), (35, 1), (44, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (22, 1), (29, 1), (33, 1), (44, 1), (55, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (22, 1), (29, 1), (35, 1), (44, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (35, 1), (56, 2)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (26, 1), (38, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (21, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (33, 1), (35, 1), (56, 2)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (33, 1), (38, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (29, 1), (33, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (26, 1), (38, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (21, 1), (35, 1), (56, 2)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (21, 1), (38, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (33, 1), (35, 1), (56, 2)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (33, 1), (38, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (32, 1), (33, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 2), (56, 2)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (59, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (35, 1), (56, 2)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (38, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (38, 1), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (35, 1), (56, 2)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (38, 1), (53, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (33, 1), (48, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 2), (35, 1), (48, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (29, 1), (33, 1), (48, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (29, 1), (35, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (32, 1), (33, 1), (42, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (32, 1), (35, 1), (42, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (33, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (35, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (8, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (33, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (35, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (32, 1), (33, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (32, 1), (35, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (33, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 2), (35, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (29, 1), (33, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (29, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (35, 1), (56, 2)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (38, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (22, 1), (33, 1), (44, 1), (48, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 2), (22, 1), (35, 1), (44, 1), (48, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (17, 1), (32, 1), (33, 1), (42, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (17, 1), (32, 1), (35, 1), (42, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (22, 1), (29, 1), (33, 1), (44, 1), (48, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (22, 1), (29, 1), (35, 1), (44, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component56.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component56.SelectedLeafB7
