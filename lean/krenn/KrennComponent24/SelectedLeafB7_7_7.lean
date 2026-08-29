import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f644459f8b98b9edfcb1637f3f5c09ca73f9fc4ec98fc44254b21180edf8788a"
def certificateSHA256 : String := "f5d3c9ae9da51e29937d4fa391ad5788aad1cccb3df55aa9268a5fa2650af47e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 673 := ![
  3,
  9,
  16,
  18,
  19,
  326,
  443,
  614,
  626,
  653,
  666,
  667,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(65, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (57, 1), (64, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (64, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (52, 1), (64, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (41, 1), (64, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (48, 1), (51, 1), (57, 1), (65, 1), (67, 1), (70, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1), (54, 1), (65, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(52, 1), (65, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (51, 1), (57, 1), (65, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(41, 1), (54, 1), (65, 1), (67, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (65, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (48, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (30, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (52, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (30, 1), (41, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (48, 1), (51, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (48, 1), (54, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (51, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (54, 1), (65, 1), (67, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_7_7.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_7_7
