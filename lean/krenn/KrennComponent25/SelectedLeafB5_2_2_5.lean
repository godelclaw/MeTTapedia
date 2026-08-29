import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_2_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "915702deb4b473c0b8e3e140a3b7c5936a868cb6ac7770af437f93040ab12d25"
def certificateSHA256 : String := "48ee3679bd187d85617589cb6d5d6f7fb5a1999ea9df2cdf2fff1c23f237ea10"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 668 := ![
  1,
  14,
  21,
  157,
  162,
  169,
  170,
  173,
  177,
  196,
  267,
  293,
  300,
  312,
  322,
  359,
  405,
  424,
  430,
  433,
  435,
  439,
  449,
  450,
  471,
  499,
  578,
  579,
  580,
  643,
  647,
  655,
  656,
  661,
  663,
  664,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(0, 1), (22, 1), (28, 1), (48, 1), (52, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := -2, powers := [(0, 1), (22, 1), (29, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := 2, powers := [(22, 1), (24, 1), (29, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (29, 1), (48, 1), (50, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (27, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(29, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (48, 1), (52, 1), (54, 1), (64, 1)] }, { coefficient := -2, powers := [(28, 1), (48, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (48, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (24, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (28, 1), (48, 1), (52, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := 2, powers := [(0, 1), (29, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := -2, powers := [(24, 1), (29, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (50, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 2, powers := [(48, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (28, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(24, 1), (28, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := -2, powers := [(24, 1), (29, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (48, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (28, 1), (48, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (48, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (48, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (22, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (28, 1), (48, 1), (52, 1), (54, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := -2, powers := [(2, 1), (45, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (24, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (47, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_2_2_5.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_2_2_5
