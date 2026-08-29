import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5860d7630502bc6d625df4228d1ad3766922b15d9c4f6f65d99f9e50fd28863f"
def certificateSHA256 : String := "daef37bcefbf5d5c787cfaf4bb7c6ba723116d46de5f46d993a6a4a007780ce0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 639 := ![
  0,
  1,
  2,
  3,
  5,
  163,
  165,
  187,
  189,
  193,
  197,
  198,
  344,
  346,
  350,
  351,
  352,
  353,
  372,
  468,
  471,
  490,
  496,
  502,
  503,
  557,
  558,
  598,
  608,
  635,
  637,
  638
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (51, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (52, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (35, 1), (36, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (36, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (36, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (35, 1), (40, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (35, 1), (45, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (35, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (35, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (47, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (43, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (36, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (32, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (49, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (35, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (45, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (35, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (43, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (43, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (35, 1), (40, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (35, 1), (45, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (35, 1), (40, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (35, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (47, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (36, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (45, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB7
