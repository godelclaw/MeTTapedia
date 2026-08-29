import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_4_2_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "755b01cefbb94342fad24e2184bcaba48300415ba6e1751b334ef00b2e11a737"
def certificateSHA256 : String := "c4b923cd5d55b8d31a686dac2835aebba04e9f6c2b6c4727da9a79cef378a0fc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 676 := ![
  187,
  191,
  193,
  196,
  318,
  396,
  416,
  422,
  425,
  439,
  440,
  441,
  505,
  532,
  566,
  580,
  581,
  589,
  615,
  619,
  644,
  649,
  660,
  663,
  665,
  666,
  668,
  669,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(27, 1), (44, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 2), (22, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 2), (27, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (16, 1), (44, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (16, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 2), (27, 1), (60, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (16, 1), (34, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (17, 1), (22, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (16, 1), (46, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 2), (22, 1), (60, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (17, 1), (27, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (16, 1), (27, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (60, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (60, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (64, 1)] }, { coefficient := 1, powers := [(51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (16, 1), (27, 1), (34, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (16, 1), (27, 1), (40, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (16, 1), (27, 1), (31, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (16, 1), (22, 1), (27, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (16, 1), (39, 1), (46, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (16, 1), (27, 1), (59, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (16, 1), (27, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (16, 1), (34, 1), (44, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (16, 1), (27, 1), (42, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (16, 1), (27, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 2), (22, 1), (45, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 2), (27, 1), (47, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (17, 1), (22, 1), (44, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (17, 1), (27, 1), (46, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (16, 1), (27, 1), (37, 1), (60, 1), (62, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_4_2_4_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_4_2_4_3
