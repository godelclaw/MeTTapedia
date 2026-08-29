import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dc154f72ef0cc7146a50b9780634b286bb8ccdfd39f9450a7ecbb43f6fa935fe"
def certificateSHA256 : String := "166d9e4f0e557d8c2a5d10d0fc47019adf52408970a2432a3849043b62881084"

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
  313,
  316,
  317,
  318,
  320,
  321,
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
  453,
  457,
  467,
  468,
  566,
  567,
  608,
  644,
  650,
  660,
  661,
  663,
  665,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
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
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (28, 1), (51, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1), (51, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (54, 1)] }, { coefficient := -1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(28, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (17, 1), (22, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (47, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (54, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (28, 1), (47, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (28, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (36, 1), (47, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (39, 1), (47, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (44, 1), (47, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (22, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (43, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (44, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (36, 1), (40, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (39, 1), (40, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(40, 1), (45, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (47, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (28, 1), (42, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (28, 1), (47, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (40, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_3_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_3_4
