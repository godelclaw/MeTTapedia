import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "52980df2ae641c044952fe31960349a46c0f7765a8f77ae256521571801b1795"
def certificateSHA256 : String := "9a352739bf371ab9d495f139463ba8a67bd4ff8cc4506361530f2f4fd579bbb9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 592 := ![
  1,
  2,
  4,
  17,
  29,
  169,
  227,
  335,
  336,
  365,
  367,
  429,
  475,
  519,
  540,
  585,
  587,
  588,
  589,
  590
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (38, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (38, 1), (40, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (29, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (29, 1), (35, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB6_5
