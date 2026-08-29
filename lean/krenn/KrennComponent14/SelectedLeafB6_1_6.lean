import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB6_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "47ea0a8d4762966b2d9fb35cc0fde21c727b5b7be6c74ccf9bebbf7dab87cf75"
def certificateSHA256 : String := "486848766dd0d8558967961557fb59e3511879377ed0f4d626e52648b69a114a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 643 := ![
  7,
  13,
  17,
  105,
  179,
  191,
  194,
  288,
  299,
  313,
  348,
  349,
  350,
  351,
  358,
  369,
  410,
  633,
  635,
  636,
  638,
  639,
  640,
  641,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (46, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (37, 1), (43, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (26, 1), (58, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (34, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (8, 1), (58, 1), (60, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (8, 1), (13, 1), (58, 1), (60, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (8, 1), (18, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (8, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (58, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (8, 1), (13, 1), (18, 1), (27, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (8, 1), (22, 1), (54, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (58, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (8, 1), (22, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (8, 1), (13, 1), (22, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (22, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB6_1_6.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB6_1_6
