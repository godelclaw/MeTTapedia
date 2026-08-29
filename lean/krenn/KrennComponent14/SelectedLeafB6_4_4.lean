import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB6_4_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "366be249865569bf5756169d88461310fc2943dfa8b1bca1d899bb6365179754"
def certificateSHA256 : String := "57af822680e87347e991f678d5e115eb614c3681acb6fd32db458f53a4e9cc13"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 643 := ![
  11,
  162,
  282,
  313,
  348,
  350,
  351,
  633,
  635,
  636,
  638,
  639,
  641,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (17, 1), (34, 1), (37, 1)] }],
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB6_4_4.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB6_4_4
