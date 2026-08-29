import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB6_6_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e62ede1a6a486251c7e98f2dfc2d50199291227e82f5a5aad4d567ad6e1961c7"
def certificateSHA256 : String := "e2b68a62501198171d364602875d2f71aff6b8618f17a1613da0141952b4a52c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 675 := ![
  2,
  7,
  10,
  18,
  20,
  22,
  179,
  193,
  303,
  304,
  318,
  342,
  420,
  424,
  429,
  565,
  583,
  662,
  664,
  665,
  668,
  670,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (30, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (30, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(32, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (58, 1), (60, 1), (67, 1)] }, { coefficient := 2, powers := [(3, 1), (32, 1), (50, 1), (60, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (54, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (68, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (50, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (32, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (32, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (32, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB6_6_1_5.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB6_6_1_5
