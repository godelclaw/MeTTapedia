import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_4_4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6d4094b65c2559b334e488cf3a04fced030f57e6c74e14aece36eefaeb940e10"
def certificateSHA256 : String := "971ab766e13d746099802aa5d8ce201b17631b0c79bc63fa3e8547194110699e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 668 := ![
  14,
  312,
  435,
  438,
  449,
  450,
  478,
  578,
  579,
  606,
  643,
  647,
  655,
  656,
  658,
  660,
  661,
  663,
  664,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (36, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(36, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (28, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (28, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (28, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (61, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (61, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := -1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (45, 1)] }, { coefficient := -1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 2), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (18, 1), (40, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (24, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (19, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (35, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (36, 1), (47, 1), (50, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_4_4_6.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_4_4_6
