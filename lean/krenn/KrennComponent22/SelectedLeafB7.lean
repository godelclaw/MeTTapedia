import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d8c898e3af6074bdf2d62f59f121b4ac650c06b007d0fa06430a472719f8d961"
def certificateSHA256 : String := "0add3a8b52a572885aa45afa3d7af9cdc8c18a3f2e77e06df9bdcba19cdf2b50"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 639 := ![
  0,
  1,
  2,
  3,
  18,
  166,
  219,
  225,
  237,
  345,
  347,
  363,
  364,
  369,
  371,
  374,
  388,
  635,
  637,
  638
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (17, 1), (35, 1), (36, 1), (53, 1), (58, 1), (62, 2)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (17, 1), (35, 1), (38, 1), (53, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (23, 1), (36, 1), (47, 1), (53, 1), (58, 1), (62, 2)] }, { coefficient := -1, powers := [(2, 2), (23, 1), (38, 1), (47, 1), (53, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (23, 1), (32, 1), (36, 1), (47, 1), (58, 1), (62, 2)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (23, 1), (32, 1), (38, 1), (47, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (29, 1), (38, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (29, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (22, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (29, 1), (36, 1), (38, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (29, 1), (36, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (32, 1), (36, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (29, 1), (41, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (22, 1), (38, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (22, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (36, 1), (38, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (36, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (36, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 2), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (38, 1), (59, 2)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (41, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (38, 1), (59, 2)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (41, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (36, 1), (51, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 2), (38, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (32, 1), (36, 1), (51, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (32, 1), (38, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (35, 1), (36, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (35, 1), (38, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (36, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (8, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (36, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (35, 1), (36, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (35, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (36, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 2), (38, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (32, 1), (36, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (32, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (38, 1), (59, 2)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (23, 1), (36, 1), (47, 1), (51, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 2), (23, 1), (38, 1), (47, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (17, 1), (35, 1), (36, 1), (45, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (17, 1), (35, 1), (38, 1), (45, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (23, 1), (32, 1), (36, 1), (47, 1), (51, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (23, 1), (32, 1), (38, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB7
