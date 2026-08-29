import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7314f89aae33166e3cd32e98171bbe6336d7e139226af02142490402edc244a3"
def certificateSHA256 : String := "bf0948251113c34bafc5cd68110f8b020052304dc9afb59f72b7ef4d66584681"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 670 := ![
  184,
  187,
  189,
  191,
  193,
  196,
  250,
  251,
  309,
  311,
  313,
  316,
  317,
  322,
  324,
  382,
  396,
  397,
  417,
  419,
  425,
  430,
  434,
  439,
  440,
  457,
  467,
  468,
  566,
  567,
  608,
  644,
  646,
  655,
  660,
  661,
  663,
  664,
  665,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(19, 1), (22, 1), (23, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (28, 1), (51, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (54, 1)] }, { coefficient := -1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1), (23, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (47, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (22, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (54, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (28, 1), (47, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (28, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (49, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (36, 1), (47, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (39, 1), (47, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (44, 1), (47, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (40, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (46, 1), (49, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (46, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (38, 1), (40, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (42, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(38, 1), (40, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (28, 1), (29, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (18, 1), (28, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (47, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (28, 1), (42, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (28, 1), (47, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }]
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
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_7_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_7_4
