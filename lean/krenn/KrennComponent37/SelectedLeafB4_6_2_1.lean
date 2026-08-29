import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_6_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c6465bc04de7b2a47e6cc6e1257b4cdf5fd195adce0b55e2577f789e93aba60c"
def certificateSHA256 : String := "091f021568f2c7a251c475adedeb6e632bb451aef01b64a422c60416e3322c89"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 670 := ![
  16,
  19,
  79,
  151,
  171,
  180,
  294,
  295,
  313,
  317,
  433,
  446,
  450,
  580,
  606,
  617,
  657,
  658,
  660,
  661,
  663,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(24, 1), (37, 1), (44, 1), (55, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (55, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (46, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (39, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (46, 1)] }, { coefficient := -1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (44, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (30, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (40, 1), (46, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_6_2_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_6_2_1
