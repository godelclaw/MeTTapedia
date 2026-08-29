import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_6_1_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a759f6d6fefaec5656da6151f0282e1ab33cbc51058302430d7f1775bec95823"
def certificateSHA256 : String := "2a342a172e167aa38aa17da1081174e715f4fc345fcdcf02a4b91c62da6d0162"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 673 := ![
  2,
  3,
  7,
  23,
  24,
  142,
  301,
  318,
  319,
  505,
  506,
  581,
  606,
  607,
  656,
  657,
  659,
  660,
  663,
  665,
  667,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (36, 1), (49, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (34, 1), (46, 1), (49, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (36, 1), (42, 1), (49, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1), (39, 1), (49, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (34, 1), (36, 1), (39, 1), (49, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (36, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (37, 1), (40, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (33, 1), (46, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (36, 1), (42, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (37, 1), (40, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (37, 1), (40, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (36, 1), (39, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (37, 1), (39, 1), (40, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (36, 1), (39, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (37, 1), (39, 1), (40, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (33, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (36, 1), (37, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (36, 1), (37, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (37, 1), (39, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (28, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (37, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (36, 1), (37, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (36, 1), (37, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (37, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (31, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (49, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (39, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (33, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (36, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (36, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (31, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (31, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (19, 1), (33, 1), (37, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (19, 1), (36, 1), (37, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (19, 1), (36, 1), (37, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (19, 1), (36, 1), (37, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (31, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (13, 1), (24, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (36, 1), (37, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (24, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (24, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (33, 1), (37, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (36, 1), (37, 1), (40, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (24, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (36, 1), (37, 1), (39, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (24, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (36, 1), (37, 1), (39, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (34, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (33, 1), (34, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (34, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (34, 1), (36, 1), (39, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (34, 1), (36, 1), (39, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (7, 1), (33, 1), (37, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (7, 1), (36, 1), (37, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (11, 1), (36, 1), (37, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (15, 1), (36, 1), (37, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (31, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (24, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (24, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (24, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (24, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (36, 1), (39, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_6_1_7_4.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_6_1_7_4
