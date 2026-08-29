import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "462cb73c6d4e42cd37d7164ef8fed71c4aa3d15ec52c660c3109605bec8b0bba"
def certificateSHA256 : String := "cf701814073780cb64e88543d68921c1b71f95ef0994aa50b742bb75fda280f8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 667 := ![
  1,
  4,
  6,
  7,
  8,
  9,
  33,
  184,
  193,
  225,
  285,
  309,
  318,
  326,
  430,
  434,
  440,
  566,
  570,
  650,
  660,
  662,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (40, 1), (50, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (50, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (50, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (40, 1), (44, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (45, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (27, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (40, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (21, 1), (40, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (40, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (17, 1), (40, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (40, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 2, powers := [(9, 1), (17, 1), (27, 1), (40, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1), (42, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (52, 1)] }, { coefficient := -2, powers := [(17, 1), (21, 1), (24, 1), (40, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (27, 1), (40, 1), (50, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (31, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (22, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (28, 1), (40, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB7_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB7_7
