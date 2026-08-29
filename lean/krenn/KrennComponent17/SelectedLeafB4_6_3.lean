import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "aa4488d6b7fb31360f705cd3f159290f1c0e688f49826a3828036e0d2c4a40cb"
def certificateSHA256 : String := "67ac6dc99cca71db308ad0216c40238e31603bc01086afe647d45ffcf80b872e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 611 := ![
  6,
  14,
  17,
  18,
  25,
  30,
  32,
  202,
  281,
  300,
  307,
  308,
  309,
  311,
  325,
  430,
  434,
  441,
  454,
  468,
  480,
  501,
  541,
  569,
  570,
  600,
  601,
  602,
  603,
  604,
  607,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (55, 1)] }, { coefficient := 2, powers := [(11, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (55, 1)] }, { coefficient := -2, powers := [(15, 1), (35, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (44, 1), (51, 1)] }, { coefficient := 2, powers := [(20, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (44, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (15, 1), (35, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(4, 1), (35, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (43, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (35, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (43, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (35, 1), (43, 1), (44, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (35, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (35, 1), (44, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (29, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (29, 1), (59, 1)] }, { coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 2, powers := [(3, 1), (15, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (55, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (32, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (21, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (44, 1), (54, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (40, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (40, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (47, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(41, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (21, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (21, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (21, 1), (35, 1), (44, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_6_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_6_3
