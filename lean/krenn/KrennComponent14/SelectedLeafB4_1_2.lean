import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB4_1_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "410e7eeb14a43ef1bcc4094cf99bd51048bccbffd98c6ab31ab1e65bb43adc14"
def certificateSHA256 : String := "3ea4fa8e7178af8dbc13a7f2d9d10ee7a89cdcd808f47cae425f5c0d9156d8f5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 643 := ![
  8,
  9,
  27,
  179,
  194,
  195,
  245,
  313,
  348,
  349,
  350,
  351,
  352,
  360,
  457,
  524,
  575,
  576,
  581,
  605,
  631,
  633,
  636,
  637,
  638,
  640,
  641,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (35, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (35, 1), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(34, 1), (35, 1), (40, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (35, 1), (40, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (34, 1), (40, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (40, 1), (41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (32, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (32, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 2, powers := [(46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (40, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -2, powers := [(46, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (13, 1), (23, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (34, 1), (40, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (22, 1), (42, 1), (51, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (34, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (29, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (17, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (17, 1), (34, 1), (40, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB4_1_2.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB4_1_2
