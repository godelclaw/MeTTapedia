import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_6_5_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3f2f8a9be1e86f964167ef7ead75028e228ef7c13c363b9243586f99032036d7"
def certificateSHA256 : String := "8fbbb7c06e789828cd264b20f373ee1325210cb4947b857c35f139f564aa524f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 676 := ![
  180,
  181,
  187,
  191,
  193,
  195,
  196,
  254,
  263,
  302,
  303,
  315,
  317,
  318,
  320,
  322,
  345,
  350,
  393,
  412,
  425,
  429,
  440,
  453,
  465,
  468,
  482,
  567,
  660,
  661,
  663,
  666,
  667,
  669,
  670,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 68) := ![
  [{ coefficient := 2, powers := [(24, 1), (27, 1), (47, 1), (65, 1)] }, { coefficient := 2, powers := [(34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (27, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := -2, powers := [(24, 1), (27, 1), (47, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(34, 1), (37, 1), (49, 1), (61, 1)] }, { coefficient := -2, powers := [(34, 1), (37, 1), (49, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (13, 1), (34, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 2, powers := [(5, 1), (18, 1), (34, 1), (43, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (53, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := -2, powers := [(13, 1), (17, 1), (19, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (44, 1), (47, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (19, 1), (43, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (39, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (46, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (39, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (55, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (18, 1), (49, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (19, 1), (23, 1), (43, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (46, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (49, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (28, 1), (34, 1), (43, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (44, 1), (47, 1)] }, { coefficient := 2, powers := [(16, 1), (34, 1), (37, 1), (61, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (28, 1), (43, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (53, 1), (56, 1)] }, { coefficient := 4, powers := [(17, 1), (27, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (16, 1), (34, 1), (46, 1), (51, 1)] }, { coefficient := -2, powers := [(3, 1), (16, 1), (34, 1), (46, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (21, 1), (34, 1), (43, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (21, 1), (43, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (21, 1), (39, 1), (46, 1)] }, { coefficient := -2, powers := [(17, 1), (21, 1), (46, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (52, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (17, 1), (23, 1), (49, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (18, 1), (46, 1), (49, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (21, 1), (34, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (21, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (21, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (34, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (28, 1), (34, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (28, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (27, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (16, 1), (34, 1), (51, 1)] }, { coefficient := 2, powers := [(3, 1), (16, 1), (34, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (21, 1), (39, 1)] }, { coefficient := 2, powers := [(17, 1), (21, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (17, 1), (53, 1)] }, { coefficient := -2, powers := [(13, 1), (17, 1), (23, 1), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (53, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (49, 1)] }, { coefficient := -2, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(35, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (17, 1), (27, 1), (53, 1)] }, { coefficient := -2, powers := [(3, 1), (16, 1), (24, 1), (34, 1), (51, 1)] }, { coefficient := -2, powers := [(3, 1), (16, 1), (24, 1), (34, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (23, 1), (27, 1), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (27, 1), (53, 1)] }, { coefficient := -2, powers := [(17, 1), (21, 1), (24, 1), (39, 1)] }, { coefficient := -2, powers := [(17, 1), (21, 1), (24, 1), (56, 1)] }, { coefficient := 4, powers := [(17, 1), (23, 1), (27, 1), (53, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (27, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (21, 1), (34, 1), (53, 1), (54, 1), (66, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (21, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (23, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (40, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (27, 1), (47, 1)] }, { coefficient := -2, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (49, 1)] }, { coefficient := 2, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (37, 1)] }, { coefficient := 2, powers := [(5, 1), (28, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_6_5_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_6_5_2
