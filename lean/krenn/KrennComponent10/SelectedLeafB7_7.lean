import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "819fc89dd171c7b872e47175909e1ce78ad2b7a9162b203c79f2b3c620bad9c4"
def certificateSHA256 : String := "0bb35796bf1c89aefd6b7f26adc531081b2d0afec1077fab3d73aadd7dfb4bfa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 641 := ![
  0,
  2,
  4,
  5,
  15,
  24,
  25,
  27,
  29,
  68,
  161,
  162,
  163,
  164,
  165,
  169,
  170,
  184,
  189,
  192,
  359,
  360,
  361,
  363,
  364,
  406,
  409,
  466,
  550,
  557,
  582,
  634,
  635,
  636,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (55, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (32, 1), (48, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (38, 1), (55, 1), (58, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (38, 1), (58, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (48, 1), (53, 1), (55, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (55, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (47, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (48, 1), (52, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (52, 1), (59, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (18, 1), (32, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (59, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (27, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (19, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (27, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (45, 1), (59, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (41, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(18, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (55, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (32, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(48, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(2, 1), (19, 1), (38, 1), (41, 1), (55, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (39, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 2), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (45, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (24, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (24, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (24, 1), (48, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (28, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (24, 1), (35, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (24, 1), (35, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (27, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (36, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (36, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (27, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (29, 1), (48, 1), (60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB7_7.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB7_7
