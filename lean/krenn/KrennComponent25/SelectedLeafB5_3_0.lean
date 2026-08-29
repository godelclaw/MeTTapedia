import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2cdec015f6f0033f628658251a7af5028d923457da88df449f4f7843ad44df4f"
def certificateSHA256 : String := "b30c7bdc723a1fe7b0959f5b2b08654d4e2f233b7cea9bd8d89f5cd9f96a5854"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 665 := ![
  1,
  14,
  21,
  142,
  162,
  169,
  170,
  173,
  177,
  238,
  266,
  267,
  292,
  293,
  294,
  300,
  306,
  310,
  312,
  313,
  317,
  388,
  405,
  406,
  427,
  430,
  433,
  435,
  439,
  449,
  450,
  471,
  475,
  578,
  579,
  580,
  588,
  606,
  643,
  647,
  655,
  656,
  658,
  660,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 65) := ![
  [{ coefficient := -2, powers := [(3, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (27, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(0, 1), (28, 1), (48, 1)] }, { coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (43, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (29, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (29, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (29, 1), (41, 1), (43, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(29, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (41, 1), (45, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1), (43, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(16, 1), (24, 1), (29, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (29, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (18, 1), (29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (27, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (24, 1), (28, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (27, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (24, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (27, 1), (29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (18, 1), (29, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (29, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (29, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (18, 1), (24, 1), (29, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (18, 1), (24, 1), (29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (29, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (24, 1), (29, 1), (37, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (24, 1), (29, 1), (41, 1), (45, 1), (52, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (29, 1), (41, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (29, 1), (41, 1), (52, 1)] }, { coefficient := -2, powers := [(17, 1), (29, 1), (36, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (18, 1), (24, 1), (29, 1), (37, 1), (41, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (24, 1), (29, 1), (41, 1), (45, 1), (52, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (29, 1), (41, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (29, 1), (41, 1), (52, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (36, 1), (41, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (27, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (18, 1), (24, 1), (29, 1), (40, 1), (41, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (17, 1), (18, 1), (24, 1), (29, 1), (40, 1), (41, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(16, 1), (17, 1), (18, 1), (22, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := 2, powers := [(16, 1), (17, 1), (18, 1), (27, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := 2, powers := [(16, 1), (17, 1), (22, 1), (24, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := 2, powers := [(16, 1), (17, 1), (24, 1), (27, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (41, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (41, 1), (45, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_3_0.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_3_0
