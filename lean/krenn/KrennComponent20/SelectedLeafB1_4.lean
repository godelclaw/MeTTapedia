import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "861bcf8ab9e843369b597635cb0f79f24b93d3e2a8d7f4b9971b6a13cee9c91c"
def certificateSHA256 : String := "099c1b1e63f18a0c0cf5eb92280aa3005172d60e8b7664a9746c447de7f7ff4b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 642 := ![
  15,
  23,
  163,
  183,
  187,
  188,
  193,
  196,
  198,
  199,
  317,
  346,
  350,
  352,
  353,
  364,
  369,
  437,
  468,
  484,
  506,
  591,
  598,
  621,
  635,
  636,
  638,
  640,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(28, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 2), (25, 1), (28, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (32, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (29, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (36, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (32, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (28, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (55, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(29, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (52, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (60, 1)] }, { coefficient := -1, powers := [(28, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (25, 1), (28, 1), (60, 2)] }],
  [{ coefficient := 1, powers := [(36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (25, 1), (28, 1), (37, 1), (58, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (25, 1), (28, 1), (45, 1), (51, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (47, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (43, 1), (49, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (43, 1), (51, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (49, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (49, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (43, 1), (51, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (36, 1), (47, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(36, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (18, 1), (25, 1), (28, 1), (55, 1), (60, 2)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (36, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (25, 1), (28, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (38, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (36, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (20, 1), (32, 1), (43, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (26, 1), (32, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (29, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (36, 1), (43, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (28, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (36, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (32, 1), (36, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (58, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB1_4.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB1_4
