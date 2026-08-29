import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6ac094da30dee9a6c66229b9c6dd1c83791ca7d2f2ab385d655d9d6388449cf0"
def certificateSHA256 : String := "620735f63260d3f6e31c3c89189d03f9fc21595d040b2f128b26b582672c9c27"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 639 := ![
  2,
  3,
  9,
  163,
  192,
  193,
  194,
  204,
  205,
  225,
  351,
  363,
  364,
  557,
  558,
  621,
  635,
  636,
  637,
  638
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (32, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 2), (56, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (35, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (29, 1), (35, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 2), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (22, 1), (32, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 2), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (22, 1), (35, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (35, 1), (41, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 2), (41, 2)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (17, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (16, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (12, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (35, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (32, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (32, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (32, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (35, 1), (37, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (35, 1), (40, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (35, 1), (45, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (38, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (41, 1), (56, 2), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (47, 1), (53, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (38, 1), (41, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (41, 2), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB2.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB2
