import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0a2b708d2d3d1f8db1e28c4839a19d56351877a0bece38a9f8e5e9dc21ae82cb"
def certificateSHA256 : String := "518d79e07cc1a24df0072eb3d9600ddba65505001c01f0b00b0b3e014288d915"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 12 → Fin 665 := ![
  2,
  15,
  16,
  162,
  544,
  545,
  618,
  644,
  658,
  659,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 12 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 12 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (28, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (28, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (39, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (39, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (16, 1), (22, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (18, 1), (28, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (22, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (16, 1), (28, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (24, 1), (28, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (28, 1), (39, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1), (63, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 12,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_6_1.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_6_1
