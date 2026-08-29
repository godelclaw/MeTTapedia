import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component54.SelectedLeafB2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b2fe0b82c144a7a25ea37e7b2b34c4acb89cacaf082dd4956b6258452117620d"
def certificateSHA256 : String := "446862c3a898013fbcf5bbfb464f2ceb4c84a883f60148ba65c7f16cf2663f6d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 642 := ![
  9,
  11,
  16,
  17,
  23,
  29,
  196,
  197,
  198,
  203,
  222,
  347,
  351,
  352,
  359,
  360,
  361,
  364,
  460,
  467,
  468,
  473,
  474,
  487,
  560,
  561,
  624,
  638,
  639,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(3, 1), (27, 1), (33, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (27, 1), (33, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (36, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (36, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(25, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(30, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(30, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (44, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (26, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(20, 1), (26, 1), (27, 1), (46, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (52, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (36, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (36, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (33, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (33, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (25, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (14, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (25, 1), (26, 1), (52, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (26, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (25, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (27, 1), (33, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (27, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (36, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (36, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := -1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (27, 1), (33, 1), (47, 1), (52, 2)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (27, 1), (33, 1), (47, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (33, 1), (41, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (33, 1), (41, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (41, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (41, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (41, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (41, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (44, 1), (52, 2)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (44, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (25, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (42, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (36, 1), (50, 1), (52, 2)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (36, 1), (50, 1), (52, 1), (56, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (26, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (26, 1), (46, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := -3, powers := [(6, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(26, 1), (48, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(26, 1), (48, 1), (54, 1), (56, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component54.SelectedLeafB2.selectedHasNoCommonZero

end Krenn.Component54.SelectedLeafB2
