import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "226d2114d1f8c64fec3eab00e548f7938b644760a520428e2c525dee7c3d663c"
def certificateSHA256 : String := "b902b27c5360e2e96752265f702d8ca7330728723653215cc9720312737fc2e4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 670 := ![
  15,
  27,
  28,
  171,
  179,
  180,
  181,
  411,
  433,
  438,
  449,
  450,
  453,
  454,
  487,
  566,
  619,
  657,
  663,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(23, 1), (39, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (37, 1), (52, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (61, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (54, 1), (61, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1)] }, { coefficient := -2, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1)] }]
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

#print axioms Krenn.Component37.SelectedLeafB5_2_4_2.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_4_2
