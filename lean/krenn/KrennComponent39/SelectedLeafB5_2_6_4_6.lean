import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_6_4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "87bdbf864f7d286db4e215c969a4dacd85d79240de9f0745d4eab994ff26e1a5"
def certificateSHA256 : String := "4e9f2c5d443b3a0823592709b787cba8d601686b84f210ff967a391ada6a6dc3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 676 := ![
  184,
  187,
  191,
  192,
  193,
  195,
  300,
  301,
  321,
  324,
  347,
  419,
  425,
  440,
  460,
  465,
  470,
  471,
  566,
  645,
  660,
  661,
  663,
  666,
  669,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (26, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (22, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (31, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (17, 1), (19, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 2), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (45, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (17, 1), (22, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (22, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := -2, powers := [(5, 1), (17, 1), (22, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (22, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (31, 1), (42, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (31, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (34, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (22, 1), (42, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (22, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (22, 1), (47, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 2), (22, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (22, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1)] }, { coefficient := -1, powers := [(8, 1), (17, 1), (22, 2), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_6_4_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_6_4_6
