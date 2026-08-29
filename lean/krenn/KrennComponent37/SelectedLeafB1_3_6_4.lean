import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_3_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f207e7b3aa6a526876fec7b1980e9f66f881d186b27f242f7bf467280a75cdae"
def certificateSHA256 : String := "dc33afeb6034ff0d9a7166e542423cec208cbb26322a351cfef51a92b49df29c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 670 := ![
  175,
  315,
  410,
  430,
  435,
  455,
  471,
  479,
  500,
  526,
  580,
  581,
  609,
  645,
  658,
  660,
  663,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(21, 1), (29, 1), (41, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (46, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (41, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (52, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (29, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (29, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (21, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (25, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (25, 1), (29, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (51, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (25, 1), (29, 1), (46, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (29, 1), (51, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (38, 1), (46, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (38, 1), (51, 1), (60, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (41, 1), (46, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (41, 1), (46, 1), (51, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (41, 1), (51, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (46, 2), (51, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (46, 2), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (46, 1), (53, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (51, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (41, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (46, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_3_6_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_3_6_4
