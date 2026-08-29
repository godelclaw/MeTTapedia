import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "85c4829dc9962dd2f7d9b0b1e3f80f75cb1e782e34d1c854745dc69c835e0ece"
def certificateSHA256 : String := "459e4c8cc365c448c9fddabb01e75335b1b56608e59e78d76c160b46e5f2522a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 670 := ![
  187,
  195,
  250,
  260,
  302,
  313,
  314,
  317,
  321,
  345,
  382,
  396,
  418,
  423,
  439,
  467,
  508,
  567,
  591,
  608,
  651,
  661,
  663,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (22, 1), (27, 1), (52, 1), (62, 2), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (52, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (49, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (46, 1), (49, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (16, 1), (19, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (23, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (16, 1), (41, 1), (46, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (22, 1), (27, 1), (62, 2), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (46, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (46, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (26, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (22, 1), (23, 1), (27, 1), (62, 2), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (26, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (23, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (46, 1), (52, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (51, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (23, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (22, 1), (27, 1), (62, 2), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (22, 1), (62, 2), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (23, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (52, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 2), (22, 1), (62, 2), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 3, powers := [(0, 1), (16, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (51, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (49, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (46, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(40, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (44, 1), (49, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (22, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (44, 1), (49, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (49, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (21, 1), (46, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 3), (40, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 1), (19, 1), (26, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (49, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (19, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (40, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (40, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (16, 2), (22, 1), (31, 1), (62, 2), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (19, 1), (31, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -3, powers := [(0, 1), (3, 1), (16, 1), (31, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (16, 1), (18, 1), (22, 1), (27, 1), (62, 2), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (16, 1), (21, 1), (22, 1), (62, 2), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (16, 1), (22, 1), (23, 1), (27, 1), (62, 2), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (19, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (19, 1), (21, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (23, 1), (26, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (23, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (21, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (23, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (16, 2), (21, 1), (22, 1), (49, 1), (62, 2), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (21, 1), (49, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -3, powers := [(0, 1), (16, 1), (21, 1), (46, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (23, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (49, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (52, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_7_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_7_4
