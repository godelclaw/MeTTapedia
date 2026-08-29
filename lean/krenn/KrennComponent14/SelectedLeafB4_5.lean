import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9e6a0af918cefa501084f6c34d5b5ea225692fcc1badf096c5a9c3b4c76fe94b"
def certificateSHA256 : String := "71f3335adfa5e2d5754f5f12df92a48600f3579712e601dfa8b835d47f95b644"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 640 := ![
  20,
  127,
  179,
  194,
  195,
  282,
  309,
  313,
  348,
  349,
  350,
  351,
  360,
  464,
  524,
  572,
  633,
  636,
  637,
  638
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(28, 1), (40, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (28, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (31, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(24, 1), (40, 1), (42, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [(38, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (31, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (42, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB4_5
