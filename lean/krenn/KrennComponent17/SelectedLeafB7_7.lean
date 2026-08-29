import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "db1446a131cfa1a9fa5a820505acee3fe42ad2ebcab2fe2ba38b3e7e45d29c1f"
def certificateSHA256 : String := "34a2f634177cc6736a0d48e8659827cdae28e1f5400045c9ab9f7106fcd13477"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 608 := ![
  2,
  3,
  4,
  7,
  17,
  18,
  32,
  33,
  39,
  42,
  190,
  311,
  323,
  325,
  414,
  415,
  423,
  427,
  434,
  441,
  459,
  468,
  469,
  505,
  506,
  507,
  541,
  549,
  596,
  601,
  603,
  604,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(6, 1), (13, 1), (29, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (36, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (36, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (41, 1), (45, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (41, 1), (45, 1), (57, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (36, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (36, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (29, 1), (41, 1), (50, 2), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (41, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (41, 1), (45, 1), (50, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (40, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (36, 1), (41, 1), (50, 2), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (36, 1), (41, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1), (38, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [(44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (17, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (24, 1), (40, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (24, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (41, 1), (55, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (41, 1), (51, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (41, 1), (55, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (41, 1), (51, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (23, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (27, 1), (40, 1), (41, 1), (50, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (41, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (29, 1), (41, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (29, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (36, 1), (41, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (29, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (41, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (61, 1)] }, { coefficient := -1, powers := [(27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (41, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (41, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (27, 1), (41, 1), (50, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (41, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (41, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(6, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(36, 1), (41, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (41, 1), (45, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (41, 1), (45, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (29, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (36, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := -1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (17, 1), (28, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (24, 1), (28, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (24, 1), (28, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (23, 1), (43, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (28, 1), (41, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (29, 1), (41, 1), (50, 2), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (29, 1), (41, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (28, 1), (41, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (27, 1), (40, 1), (41, 1), (43, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (27, 1), (41, 1), (45, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (41, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (27, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (27, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (36, 1), (41, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (36, 1), (41, 1), (50, 2), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (36, 1), (41, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (32, 1), (36, 1), (38, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (36, 1), (41, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB7_7.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB7_7
