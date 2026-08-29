import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c235cf8efa4d475eb801e08f9cf9814e9d175b8d80ad8e7e69c93d2f6a1a24da"
def certificateSHA256 : String := "32038c857fac1d5bab350fd02348c0de34c37c666a5c81506f0c21e6d1044ae6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 667 := ![
  8,
  12,
  16,
  19,
  149,
  151,
  167,
  171,
  175,
  178,
  179,
  180,
  183,
  285,
  394,
  414,
  433,
  438,
  446,
  450,
  475,
  520,
  566,
  608,
  652,
  657,
  658,
  660,
  661,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (29, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (53, 1), (58, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (45, 1), (51, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (45, 1), (51, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (55, 1), (58, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (47, 1), (58, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (58, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (45, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (29, 1), (49, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (28, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (45, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (34, 1), (51, 1), (58, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_6_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_6_7
