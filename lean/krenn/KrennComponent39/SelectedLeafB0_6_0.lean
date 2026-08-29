import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "631d9a96d96e071582ee124c067549312585b04cc1cc3d3c0f9317268fae6dfc"
def certificateSHA256 : String := "5ae6d96e233b6151bc32355dcc71247d7edb589bd8ef0b591e67f199c78fe8b0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 670 := ![
  184,
  187,
  188,
  189,
  191,
  192,
  193,
  196,
  250,
  313,
  317,
  322,
  382,
  419,
  425,
  430,
  434,
  440,
  457,
  467,
  468,
  567,
  608,
  637,
  660,
  661,
  663,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (18, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (18, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (28, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (27, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (28, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (49, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_6_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_6_0
