import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "93d25126ee1ce2a69f7c616123f0c5d3646ca432350d5f317d97c84f37a44aaf"
def certificateSHA256 : String := "195458feefe02238949883a14f17f8cb2d98f3d46692440e522846da36135c6d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 673 := ![
  11,
  16,
  22,
  23,
  30,
  31,
  192,
  197,
  277,
  301,
  304,
  305,
  316,
  318,
  360,
  419,
  430,
  434,
  440,
  515,
  563,
  602,
  603,
  659,
  660,
  662,
  663,
  666,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := -4, powers := [(7, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -2, powers := [(7, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -2, powers := [(14, 1), (31, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (45, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := -2, powers := [(7, 1), (31, 1), (33, 1), (37, 1), (45, 1), (65, 1)] }, { coefficient := 2, powers := [(10, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (42, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -2, powers := [(14, 1), (31, 1), (37, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (17, 1), (31, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (31, 1), (51, 1)] }, { coefficient := -2, powers := [(14, 1), (17, 1), (31, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (31, 1), (37, 1), (51, 1)] }, { coefficient := -2, powers := [(17, 1), (31, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (31, 1), (37, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (31, 1), (33, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (17, 1), (25, 1), (31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 4, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 2, powers := [(7, 1), (31, 1), (51, 1)] }, { coefficient := 2, powers := [(14, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(17, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (25, 1), (31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(10, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (25, 1), (28, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 2, powers := [(17, 1), (25, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(10, 1), (17, 1), (31, 1), (37, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(17, 1), (31, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (31, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (31, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (31, 1), (37, 1), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := -4, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (44, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (30, 1), (31, 1), (36, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(7, 1), (16, 1), (31, 1), (33, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (28, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (17, 1), (25, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 2, powers := [(10, 1), (17, 1), (25, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (25, 1), (31, 1), (37, 1), (39, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (25, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (25, 1), (31, 1), (37, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_2_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_2_7
