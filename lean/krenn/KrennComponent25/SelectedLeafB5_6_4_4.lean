import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_6_4_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ffe2c70bf86dd02f62a1912967a1b727b7b911f530c86b48c255baeed28ed7c7"
def certificateSHA256 : String := "3ea35a136ec0a1fd77d77394a1a856f30790fe57f24b1a49a895b9f4a8fd4dfa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 668 := ![
  1,
  14,
  142,
  168,
  293,
  294,
  300,
  312,
  430,
  435,
  438,
  450,
  478,
  579,
  580,
  606,
  607,
  628,
  655,
  656,
  661,
  663,
  664,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (23, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (35, 1), (36, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (36, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (35, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (24, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (35, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (22, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (35, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (35, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (35, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (23, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (43, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (43, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (43, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (24, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (35, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (23, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (18, 1), (35, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (35, 1), (36, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (24, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 2), (35, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (18, 1), (24, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (18, 1), (19, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 2), (23, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (36, 1), (41, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (24, 1), (41, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (18, 1), (41, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (32, 1), (59, 1), (61, 1)] }, { coefficient := -3, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (23, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (18, 1), (32, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (22, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (32, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (24, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (36, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (36, 1), (47, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (36, 1), (47, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (24, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (24, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (24, 1), (47, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (24, 1), (47, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (18, 1), (47, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (47, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (47, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (47, 1), (50, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_6_4_4.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_6_4_4
