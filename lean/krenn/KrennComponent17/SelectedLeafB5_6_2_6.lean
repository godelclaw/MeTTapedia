import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dcfe1d4ab0b538090179c0dcf1d7510c630ca43e17fe46a80d597042178a8ad6"
def certificateSHA256 : String := "a92c0a76512519835a9f71f8aa396bf1d675115f169ea22d6969671989eb7bdb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 614 := ![
  5,
  7,
  25,
  32,
  36,
  211,
  325,
  327,
  434,
  436,
  468,
  486,
  541,
  601,
  602,
  604,
  607,
  610,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (36, 1), (43, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (43, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (36, 1), (43, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (47, 1), (57, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_2_6.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_2_6
