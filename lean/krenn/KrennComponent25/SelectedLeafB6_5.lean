import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a1407430b67b5b827e1a3015b3965e522b3251d767f50ea9b611af7bc20c4f93"
def certificateSHA256 : String := "95f9d6c2175e24f9ca2101aaf4ab8185a61df7f7d5505309dc2be145d01ed542"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 662 := ![
  1,
  12,
  14,
  21,
  148,
  162,
  163,
  169,
  173,
  175,
  196,
  300,
  310,
  312,
  406,
  450,
  478,
  488,
  578,
  587,
  655,
  657,
  658,
  659,
  660
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (48, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (16, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (54, 1)] }, { coefficient := -1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (48, 1)] }, { coefficient := -1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (29, 1), (41, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB6_5
