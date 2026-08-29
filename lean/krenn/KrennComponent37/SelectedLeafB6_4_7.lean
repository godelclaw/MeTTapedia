import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "201b9d762af60e3673be13740a9ecf573d6907c81436905e9569b7697531d385"
def certificateSHA256 : String := "e9e0224724d9d1a092aa4eaacc50d9fc3bbbf5a025208bc4311f0fb0e277bf66"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 667 := ![
  0,
  1,
  3,
  4,
  12,
  16,
  19,
  29,
  171,
  269,
  309,
  311,
  446,
  450,
  566,
  650,
  652,
  657,
  659,
  660,
  661,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (29, 1), (58, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (58, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (58, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (58, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (58, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (58, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (51, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1), (58, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (53, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (53, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (58, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (58, 1), (63, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (58, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (58, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1), (58, 1), (67, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (29, 1), (48, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(12, 1), (21, 1), (29, 1), (45, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (54, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (48, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (45, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (58, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (24, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (53, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (53, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (56, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 2), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (58, 1), (67, 1)] }, { coefficient := -2, powers := [(17, 1), (28, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (24, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_4_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_4_7
