import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB7_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d76631572c1e749a2c5fbf09693a6580b5091eb7f396312caf5ad8aa3b591076"
def certificateSHA256 : String := "d9cc695ba8b4ca98324bdbfe167612b61330073cdfcd3db912570e2d5f4cf23c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 608 := ![
  2,
  3,
  4,
  5,
  18,
  30,
  32,
  40,
  183,
  188,
  300,
  309,
  311,
  325,
  358,
  434,
  441,
  465,
  466,
  495,
  552,
  556,
  601,
  602,
  603,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (22, 1), (50, 1), (58, 1), (60, 2), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (22, 1), (26, 1), (58, 1), (60, 2), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (35, 1), (60, 2), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (29, 1), (50, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (26, 1), (29, 1), (57, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (43, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (50, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (26, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (35, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (22, 1), (50, 1), (51, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (35, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (26, 1), (51, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB7_2.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB7_2
