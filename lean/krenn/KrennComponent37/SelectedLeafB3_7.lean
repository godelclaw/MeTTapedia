import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d098751bf3cc2dc3372d2579a562532a32f9c6c1a71419390102969a94ce664e"
def certificateSHA256 : String := "c4189b16703acc6ef42d54f2b34b3716df20c800d4a9d61725a012fa7c8331c2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 664 := ![
  1,
  3,
  4,
  16,
  19,
  31,
  171,
  181,
  294,
  310,
  349,
  440,
  445,
  449,
  450,
  453,
  466,
  472,
  487,
  503,
  566,
  581,
  619,
  628,
  645,
  649,
  657,
  658,
  659,
  661,
  662
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (48, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (47, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (42, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (46, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (46, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (54, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(29, 1), (42, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 1), (48, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (52, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (52, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (41, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (40, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB3_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB3_7
