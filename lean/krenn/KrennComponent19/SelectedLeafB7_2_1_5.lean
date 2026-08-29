import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB7_2_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0e56b837503aafe85baf1d27d4a952c3b583f0ca77d62884960a60bf4ec91101"
def certificateSHA256 : String := "e58dade5174afb7fc8832326ccb04a5a0b3a15f919dd6519c5861dfcbf43d118"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 675 := ![
  0,
  3,
  7,
  9,
  10,
  14,
  18,
  20,
  22,
  173,
  179,
  193,
  196,
  303,
  318,
  320,
  342,
  349,
  420,
  424,
  425,
  429,
  464,
  491,
  565,
  583,
  662,
  663,
  664,
  668,
  670,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (30, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (30, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(38, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(32, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (41, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (25, 1), (60, 2)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (58, 1), (60, 1), (67, 1)] }, { coefficient := 2, powers := [(3, 1), (32, 1), (50, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(38, 1), (39, 1), (41, 1), (60, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (22, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (39, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (30, 1), (46, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (39, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (46, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (54, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (8, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (21, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (8, 1), (25, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (41, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (26, 1), (32, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (8, 1), (25, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (32, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (38, 1), (39, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB7_2_1_5.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB7_2_1_5
