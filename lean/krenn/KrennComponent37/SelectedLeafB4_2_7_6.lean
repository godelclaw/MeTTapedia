import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_2_7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "91909138d117812dade976a3701fde676de4a7e613cc54f8d382001676206dd3"
def certificateSHA256 : String := "ed3154f912f4cd9b203e748ac1bb6253b33dbcd465dcf1a9bf0bed690fd70685"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 670 := ![
  9,
  15,
  20,
  25,
  26,
  150,
  179,
  180,
  181,
  301,
  302,
  308,
  311,
  429,
  433,
  438,
  447,
  450,
  454,
  499,
  566,
  602,
  603,
  617,
  627,
  629,
  650,
  655,
  657,
  660,
  661,
  663,
  665,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 69) := ![
  [{ coefficient := -2, powers := [(0, 1), (36, 1), (37, 1), (39, 1), (59, 1), (68, 1)] }, { coefficient := 2, powers := [(20, 1), (36, 1), (37, 1), (39, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (47, 1), (68, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1), (58, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (28, 1), (39, 1), (44, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (37, 1), (39, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := -2, powers := [(20, 1), (28, 1), (39, 1), (44, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := -2, powers := [(20, 1), (36, 1), (37, 1), (39, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (53, 1), (58, 1), (65, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -2, powers := [(33, 1), (34, 1), (37, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (33, 1), (39, 1), (50, 1), (68, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (33, 1), (39, 1), (50, 1), (68, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (31, 1), (39, 1), (51, 1), (68, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (33, 1), (39, 1), (50, 1), (68, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (31, 1), (39, 1), (51, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (28, 1), (39, 1), (59, 1), (68, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (28, 1), (39, 1), (59, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (19, 1), (20, 1), (23, 1), (39, 1), (51, 1), (60, 1), (68, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (20, 1), (28, 1), (39, 1), (51, 1), (60, 1), (68, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (33, 1), (39, 1), (56, 1), (68, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (33, 1), (39, 1), (43, 1), (68, 1)] }, { coefficient := 2, powers := [(19, 1), (33, 1), (34, 1), (37, 1), (39, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (19, 1), (20, 1), (39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (19, 1), (20, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (31, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 2, powers := [(20, 1), (39, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (20, 1), (39, 1), (59, 1)] }, { coefficient := -2, powers := [(19, 1), (31, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (20, 1), (39, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (33, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := -2, powers := [(20, 1), (39, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (20, 1), (39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (37, 1), (39, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(20, 1), (37, 1), (39, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (19, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (20, 1), (23, 1), (27, 1), (39, 1), (51, 1), (60, 1), (68, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (20, 1), (27, 1), (28, 1), (39, 1), (51, 1), (60, 1), (68, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (27, 1), (33, 1), (39, 1), (56, 1), (68, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (27, 1), (33, 1), (39, 1), (43, 1), (68, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -2, powers := [(19, 1), (27, 1), (33, 1), (34, 1), (37, 1), (39, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (28, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (36, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (28, 1), (39, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (36, 1), (37, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (33, 1), (39, 1), (43, 1), (50, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (23, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (28, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (20, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (33, 1), (34, 1), (37, 1), (39, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (28, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (36, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (28, 1), (39, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (36, 1), (37, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (33, 1), (39, 1), (43, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (31, 1), (39, 1), (43, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (33, 1), (39, 1), (43, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (31, 1), (39, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_2_7_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_2_7_6
