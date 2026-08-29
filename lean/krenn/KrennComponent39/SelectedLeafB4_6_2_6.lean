import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_6_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "53edd76193f630f5205023eccd0bc89a210b9cb5a4098427b6702638fff86ccc"
def certificateSHA256 : String := "a164ff6bdcc719fd36eb653cc9f46548024123848b4d5dffc027b83c3b917828"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 673 := ![
  10,
  16,
  22,
  191,
  192,
  304,
  305,
  419,
  425,
  429,
  434,
  439,
  440,
  502,
  523,
  529,
  602,
  603,
  659,
  660,
  662,
  663,
  666,
  668,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(4, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (34, 1), (39, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (34, 1), (44, 2), (51, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(7, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 2, powers := [(10, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := -2, powers := [(14, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (14, 1), (34, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(4, 1), (19, 1), (20, 1), (34, 1), (39, 1), (54, 1), (66, 1)] }, { coefficient := -2, powers := [(4, 1), (19, 1), (20, 1), (34, 1), (44, 1), (54, 1), (66, 1)] }, { coefficient := 2, powers := [(4, 1), (20, 1), (34, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := -2, powers := [(4, 1), (34, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (19, 1), (20, 1), (34, 1), (39, 1), (44, 1), (54, 1), (66, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (19, 1), (20, 1), (34, 1), (44, 2), (54, 1), (66, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (19, 1), (25, 1), (34, 1), (39, 1), (44, 2), (54, 1), (64, 1), (66, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (19, 1), (25, 1), (34, 1), (44, 3), (54, 1), (64, 1), (66, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (20, 1), (34, 1), (44, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (25, 1), (34, 1), (44, 2), (46, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (34, 1), (44, 2), (46, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (25, 1), (34, 1), (44, 2), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (19, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (19, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (19, 1), (25, 1), (34, 1), (44, 2), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (34, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (34, 1), (44, 2), (54, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (10, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (39, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (44, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (6, 1), (10, 1), (30, 1), (34, 1), (44, 2), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(4, 1), (16, 1), (20, 1), (34, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (16, 1), (19, 1), (20, 1), (34, 1), (39, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (16, 1), (19, 1), (20, 1), (34, 1), (44, 2), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (16, 1), (19, 1), (25, 1), (34, 1), (39, 1), (44, 2), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (16, 1), (19, 1), (25, 1), (34, 1), (44, 3), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (16, 1), (20, 1), (34, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (16, 1), (25, 1), (34, 1), (44, 2), (46, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1), (49, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_6_2_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_6_2_6
