import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4a6a722e2a3324ee5e35524b49d5e68a98866d39c94f42a676910e5eabcbf1f5"
def certificateSHA256 : String := "db110447afef392045c2d8d04ec87537db7be72d66dc3c62e9880d235896735f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 670 := ![
  9,
  15,
  26,
  28,
  179,
  180,
  181,
  279,
  294,
  296,
  429,
  433,
  438,
  465,
  487,
  541,
  566,
  607,
  617,
  657,
  658,
  660,
  663,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(36, 1), (37, 1), (39, 1), (60, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (25, 1), (44, 1), (55, 1), (60, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (44, 1), (55, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (44, 1), (51, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (39, 1), (51, 1), (60, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (24, 1), (26, 1), (60, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (25, 2), (53, 1), (60, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (51, 1), (60, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (39, 1), (60, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (55, 1), (60, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (37, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (37, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (55, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (44, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (37, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (24, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (24, 1), (26, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (25, 1), (44, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 2), (44, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (44, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (39, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1), (39, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (37, 1), (44, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (37, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (37, 1), (42, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_6_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_6_6
