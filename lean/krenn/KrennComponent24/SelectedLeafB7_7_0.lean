import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6e0e8185604d52d7c4186e3170ac4c93542cd955ad4012c9a4a4632568445b51"
def certificateSHA256 : String := "1d3f5330c3c21d9365c87515e4cfd22e08572196ee201bb63341107167159fe8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 673 := ![
  135,
  232,
  301,
  406,
  443,
  447,
  486,
  549,
  550,
  564,
  614,
  665,
  669,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(22, 1), (48, 1), (54, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (28, 1), (48, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (48, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (48, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (28, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (51, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (28, 1), (51, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (28, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (43, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (48, 1), (51, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (21, 1), (51, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (22, 1), (48, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (22, 1), (63, 1), (67, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_7_0.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_7_0
