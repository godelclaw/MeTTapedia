import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_6_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9ed485dae6754dad56ef0f3e7d7e68a37f5d0580a37d5a6b3bfd66db66c5a0c7"
def certificateSHA256 : String := "1903241e07382a939af1e82dbe83c40ad5ea9306353ae0925eb349a63d8143c0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 676 := ![
  17,
  21,
  25,
  26,
  65,
  110,
  171,
  173,
  175,
  176,
  207,
  304,
  305,
  306,
  318,
  351,
  352,
  379,
  391,
  416,
  422,
  426,
  439,
  474,
  580,
  600,
  601,
  603,
  612,
  658,
  659,
  662,
  663,
  664,
  670,
  671,
  672,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (26, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (26, 1), (56, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (27, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(14, 1), (27, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (42, 1), (56, 1), (59, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (26, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (27, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (27, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1), (32, 1), (33, 1), (36, 1), (66, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 2), (33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (23, 2), (32, 1), (33, 1), (36, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (32, 1), (33, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1), (53, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (56, 1), (59, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(39, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (23, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (23, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (29, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(23, 1), (30, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (20, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (29, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (26, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (26, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (30, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (23, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(36, 1), (59, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (44, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := -1, powers := [(45, 1), (52, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (33, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (30, 1), (32, 1), (36, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (23, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (33, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (23, 1), (32, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (59, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (10, 1), (23, 2), (33, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (23, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (23, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (33, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (23, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (23, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (18, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (23, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (23, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (20, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (23, 2), (32, 1), (33, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (23, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_6_5_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_6_5_3
