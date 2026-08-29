import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_3_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "19470966cce344600290067873a7de9c1420e0fa482f35040a0709583b104993"
def certificateSHA256 : String := "199005cd689a1f0faf95669e3a70ec1920160a98ba29eaad762e85334e196f30"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 13 → Fin 670 := ![
  312,
  315,
  401,
  467,
  471,
  478,
  609,
  647,
  651,
  658,
  663,
  664,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 13 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 13 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (41, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (21, 1), (46, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (42, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (45, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 13,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_3_6_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_3_6_5
