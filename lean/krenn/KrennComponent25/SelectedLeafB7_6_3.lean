import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB7_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "79bc444950b7d3118dd652303fa7b61bf8f8ecc992fb3f241ff4c81d1802409a"
def certificateSHA256 : String := "2391a969af498c9543af3cd8854b29c0a561cd3c25e6681d6fe937e59f19920a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 665 := ![
  1,
  2,
  12,
  14,
  15,
  16,
  17,
  21,
  148,
  152,
  162,
  170,
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
  657,
  659,
  661,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
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
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(23, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (48, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (20, 1), (23, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (52, 1), (53, 1), (57, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (53, 1), (56, 1), (57, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (36, 1), (52, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (36, 1), (56, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(22, 1), (38, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (53, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (47, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (52, 1), (56, 1), (57, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (29, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (48, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (52, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (12, 1), (29, 1), (48, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (52, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (23, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (52, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (53, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (29, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (29, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (24, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (29, 1), (53, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB7_6_3.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB7_6_3
