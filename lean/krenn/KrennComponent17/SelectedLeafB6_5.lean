import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8dd217a519d1ae3f7d887f638d230ecde6fe4fc6e321ce9fdf52c6a652795754"
def certificateSHA256 : String := "58c10ca5103708e69289edb56f15ed16ef17e2fffbe5585779b3b502058669d1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 608 := ![
  2,
  3,
  4,
  18,
  32,
  33,
  42,
  311,
  314,
  325,
  415,
  423,
  434,
  436,
  441,
  459,
  488,
  541,
  572,
  598,
  601,
  603,
  604,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (35, 1), (36, 1), (41, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (29, 1), (41, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (27, 1), (41, 1), (51, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (36, 1), (41, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (41, 1), (43, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (29, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (24, 1), (29, 1), (41, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (41, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (29, 1), (41, 1), (45, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB6_5
