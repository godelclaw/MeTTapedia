import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "33c9797901070497de1d6638402becfbf6f9ff50c641193262b676b257a033f6"
def certificateSHA256 : String := "412188ac8a5c3dd0a26288f142b981a9e345badab8b3c8d89a98ade1900154cf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 669 := ![
  2,
  4,
  5,
  13,
  14,
  22,
  23,
  24,
  27,
  28,
  172,
  173,
  174,
  198,
  220,
  318,
  329,
  342,
  412,
  468,
  486,
  520,
  565,
  610,
  662,
  664,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (32, 1), (37, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (6, 1), (32, 1), (37, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (7, 1), (24, 1), (37, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (7, 1), (32, 1), (37, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (28, 1), (35, 1), (37, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (22, 1), (37, 1), (38, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (6, 1), (19, 1), (37, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (7, 1), (19, 1), (37, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (13, 1), (37, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (35, 1), (37, 1), (49, 1), (54, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (35, 1), (37, 1), (49, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (7, 1), (37, 1), (54, 1), (60, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (37, 1), (54, 1), (61, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (17, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (35, 1), (37, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (37, 1), (38, 1), (63, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (25, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (8, 1), (37, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (37, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (20, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (37, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (35, 1), (37, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (6, 1), (37, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (7, 1), (37, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (37, 1), (54, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (13, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (35, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (37, 1), (38, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (35, 1), (37, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (6, 1), (37, 1), (41, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (7, 1), (37, 1), (41, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (37, 1), (41, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (37, 1), (44, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (37, 1), (50, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (7, 1), (35, 1), (37, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (26, 1), (35, 1), (37, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (27, 1), (35, 1), (37, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (7, 1), (30, 1), (37, 1), (54, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (26, 1), (35, 1), (37, 1), (49, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (27, 1), (35, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (30, 1), (37, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (63, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB6_1
