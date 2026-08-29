import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "969b68bca687a504d2f17c91e36c1878c0d5f114160173e671977322b5c949b9"
def certificateSHA256 : String := "6eb5dfc6c5f789392638dbe04c94ba4455e0e0f5fec7ea9a4fe5d9b1f571fd18"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 665 := ![
  1,
  2,
  14,
  15,
  16,
  17,
  21,
  142,
  152,
  162,
  170,
  175,
  300,
  311,
  312,
  388,
  429,
  430,
  435,
  438,
  439,
  450,
  475,
  478,
  648,
  655,
  659,
  661,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(23, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (48, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (52, 1), (53, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (53, 1), (56, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (36, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (36, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (38, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (47, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (48, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (52, 1), (56, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (40, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (29, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (48, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (48, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (52, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (48, 1), (54, 1), (66, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (40, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (23, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (40, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (12, 1), (29, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (52, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (23, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (52, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (53, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (29, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (29, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (24, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (23, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (29, 1), (53, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (54, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_6_3.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_6_3
