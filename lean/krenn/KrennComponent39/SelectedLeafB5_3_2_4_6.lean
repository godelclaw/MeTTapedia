import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_3_2_4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1ef2148298c43138f9831a3b27226feb591bf61b4434e96c9c9f58fe673370a9"
def certificateSHA256 : String := "6e8fa3e483cd34f389584fc2a511896d618aff9889bd0e213c7d6ed929918916"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 676 := ![
  19,
  173,
  175,
  187,
  191,
  268,
  304,
  305,
  363,
  416,
  422,
  425,
  439,
  440,
  473,
  479,
  511,
  537,
  602,
  603,
  659,
  660,
  662,
  663,
  666,
  669,
  670,
  671,
  672,
  673,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (30, 1), (51, 1), (56, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (20, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (39, 1), (56, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (56, 1), (64, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (30, 1), (56, 1), (62, 1), (66, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (30, 1), (51, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (56, 2), (62, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (27, 1), (30, 1), (56, 1), (62, 1), (66, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (30, 1), (51, 1), (56, 1), (62, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(30, 1), (39, 1), (56, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (56, 1), (64, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (34, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (56, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (56, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1), (30, 1), (56, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (17, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1), (66, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (23, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (30, 1), (56, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(39, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (30, 1), (44, 1), (56, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (30, 1), (51, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (39, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (56, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (22, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (56, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (27, 1), (30, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (20, 1), (56, 2)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (56, 2), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (27, 1), (30, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (51, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (39, 1), (40, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (33, 1), (36, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (33, 1), (36, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (33, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (36, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_3_2_4_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_3_2_4_6
