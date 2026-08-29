import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB1_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0fe8f1c7a0d1e3eac2749cc8cba7e078de4e16181b335022335f53d428271e25"
def certificateSHA256 : String := "bf025e18b4c630def81cf29659479bb324a858054e911c938454ebdad7135ea7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 608 := ![
  7,
  17,
  18,
  32,
  41,
  190,
  206,
  214,
  311,
  325,
  334,
  414,
  427,
  432,
  434,
  441,
  445,
  446,
  468,
  469,
  470,
  484,
  506,
  541,
  549,
  550,
  593,
  595,
  601,
  602,
  604,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (29, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (36, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (25, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (38, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (47, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (38, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (40, 2), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (40, 1), (44, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(28, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (37, 1), (47, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (37, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (29, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (37, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(22, 1), (59, 1)] }, { coefficient := -2, powers := [(24, 1), (28, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 2), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (24, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (38, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (40, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (28, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (28, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (28, 1), (40, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (37, 1), (44, 1), (47, 1), (52, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (35, 1), (37, 1), (44, 1), (52, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (36, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (29, 1), (47, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (36, 1), (47, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (28, 1), (40, 1), (44, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (28, 1), (40, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (28, 1), (44, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (28, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (37, 1), (44, 1), (52, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 2), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := -1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (37, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (37, 1), (57, 1), (60, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB1_2.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB1_2
