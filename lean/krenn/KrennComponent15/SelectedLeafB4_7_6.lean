import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB4_7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "83bf5f4b97ac6b350195d10d74784f9dc30388093273ec9cc8a0b6f52e5ba309"
def certificateSHA256 : String := "2b09c803425ae9fe6c0e05844ba153bc9371668455e253ec4de3e446660a1aca"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 595 := ![
  17,
  21,
  29,
  33,
  178,
  234,
  318,
  335,
  362,
  365,
  366,
  367,
  368,
  400,
  413,
  475,
  519,
  585,
  586,
  588,
  589,
  590,
  592,
  594
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(51, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(3, 1), (29, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (41, 1), (44, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (23, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (44, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (38, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (20, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (21, 1), (37, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (21, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB4_7_6.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB4_7_6
