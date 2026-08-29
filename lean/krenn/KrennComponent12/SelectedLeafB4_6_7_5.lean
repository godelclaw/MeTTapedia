import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB4_6_7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dd88c5a42dce690673d9dbf58d76101e0c4768fc2542eaf4418df152818a54f3"
def certificateSHA256 : String := "2fbb667a14ffbd1185b374f73a27f3d6b40d475fa9f071669a51389cffc286bd"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 625 := ![
  11,
  13,
  17,
  23,
  27,
  32,
  43,
  192,
  218,
  308,
  312,
  335,
  336,
  338,
  339,
  340,
  350,
  396,
  407,
  464,
  579,
  611,
  612,
  614,
  615,
  616,
  618,
  620,
  621,
  622,
  623,
  624
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (50, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (49, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (31, 1), (42, 1), (54, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (33, 1), (50, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (33, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (31, 1), (54, 1), (55, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (50, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (54, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (47, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (26, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (20, 1), (31, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (31, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB4_6_7_5.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB4_6_7_5
