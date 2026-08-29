import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB4_6_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "10b4d401e4dacc6211432c97d8787cb2702dd380e1108e93a0ac84abdd01e101"
def certificateSHA256 : String := "755e9b9aaceca050c1dc21643608fcabf253da90ddbbd819496a6c67447ac3bb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 675 := ![
  6,
  11,
  12,
  236,
  328,
  329,
  330,
  332,
  341,
  342,
  346,
  375,
  377,
  448,
  453,
  455,
  462,
  494,
  499,
  589,
  651,
  662,
  665,
  666,
  667,
  668,
  670,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (33, 1), (57, 1), (68, 1)] }, { coefficient := -2, powers := [(3, 1), (30, 1), (36, 1), (54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 2), (49, 1), (59, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (36, 1), (39, 1), (59, 1), (66, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (30, 1), (47, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (52, 1), (62, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (54, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (49, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 2), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (52, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (30, 1), (59, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (46, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (52, 1), (62, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (29, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := 2, powers := [(25, 1), (30, 1), (52, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (44, 1), (52, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1), (65, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(29, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (52, 1), (65, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (30, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (53, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (51, 1), (62, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (52, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (52, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (29, 1), (44, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := -2, powers := [(25, 1), (30, 1), (44, 1), (52, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (53, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (39, 1), (59, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (49, 1), (54, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (29, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (30, 1), (52, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (30, 1), (57, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (30, 1), (36, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (30, 2), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (29, 1), (40, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (29, 1), (31, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (18, 1), (29, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (29, 1), (53, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (25, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (29, 1), (51, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (29, 1), (44, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := 2, powers := [(18, 1), (25, 1), (30, 1), (44, 1), (52, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (44, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(22, 1), (25, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (52, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (30, 2), (49, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (30, 1), (36, 1), (39, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB4_6_5_7.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB4_6_5_7
