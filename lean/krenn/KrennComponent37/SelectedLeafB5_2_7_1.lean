import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4ce643005aa9878329756d3faf96988a5f28e8066cbace6d3b4c90d22ec34d74"
def certificateSHA256 : String := "513cce78bcd0c8509d8b4a943f89ed9cb3b58952baf4425d0114487fb00a2208"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 670 := ![
  23,
  154,
  283,
  298,
  299,
  312,
  410,
  487,
  505,
  510,
  532,
  589,
  604,
  605,
  656,
  659,
  660,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(10, 1), (44, 1), (52, 1), (67, 1)] }, { coefficient := 2, powers := [(10, 1), (44, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (32, 1), (38, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (37, 1), (41, 1), (54, 1), (57, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (52, 1), (67, 1)] }, { coefficient := -2, powers := [(10, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (22, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (41, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (35, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (35, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (41, 1)] }, { coefficient := -1, powers := [(22, 1), (46, 1)] }, { coefficient := -1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1), (41, 2)] }, { coefficient := 1, powers := [(35, 1), (37, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (32, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (37, 1), (41, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(22, 1), (68, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1), (41, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (32, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (37, 1), (41, 1), (57, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (30, 1), (32, 1), (38, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (35, 1), (37, 1), (41, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (30, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (35, 1), (37, 1), (41, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (35, 1), (37, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (37, 1), (41, 2), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (37, 1), (41, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (37, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (23, 1), (35, 1), (41, 2), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (23, 1), (35, 1), (41, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (28, 1), (35, 1), (41, 2), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (28, 1), (35, 1), (41, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (46, 2)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (29, 1), (32, 1), (38, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (35, 1), (37, 1), (41, 1), (54, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (41, 2), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (41, 1), (46, 2)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (41, 2)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1), (41, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (41, 3)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (41, 2), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (41, 2), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1)] }, { coefficient := -1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (37, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (41, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (37, 1), (41, 2)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (37, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (37, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_7_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_7_1
