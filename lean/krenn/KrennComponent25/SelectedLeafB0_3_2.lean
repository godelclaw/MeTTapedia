import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB0_3_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "27adf0256a09cf20af67a7c65c17184b242b39b33abc31333d40ff4f4959e44a"
def certificateSHA256 : String := "c0df75ee056f0074afe531b55d66ca645c155bc98aa470d4dfea870d07e464c8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 665 := ![
  1,
  21,
  177,
  294,
  300,
  312,
  319,
  424,
  450,
  461,
  467,
  469,
  478,
  578,
  579,
  609,
  655,
  656,
  658,
  660,
  661,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (52, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (48, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (52, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (50, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (50, 1), (56, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (23, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (23, 1), (56, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (52, 2), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (52, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (56, 2), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (56, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (56, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(47, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (56, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(45, 1), (56, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (52, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (61, 1)] }, { coefficient := 1, powers := [(56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(52, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(56, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (35, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (45, 1), (52, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (45, 1), (54, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (23, 1), (45, 1), (52, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (23, 1), (45, 1), (54, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (52, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (56, 2), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (47, 1), (50, 1), (52, 2), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (47, 1), (50, 1), (52, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (53, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (45, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (45, 1), (53, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (45, 1), (52, 1), (53, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (45, 1), (53, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (52, 2), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (50, 1), (52, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (56, 2), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (53, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1), (52, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1), (56, 2), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1), (50, 1), (52, 2), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1), (50, 1), (52, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (53, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 2), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(45, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(45, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(47, 1), (52, 1), (53, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (48, 1), (52, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (48, 1), (54, 1), (56, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1), (61, 1)] }, { coefficient := 1, powers := [(56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (41, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (41, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (23, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (23, 1), (56, 1), (59, 1), (61, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB0_3_2.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB0_3_2
