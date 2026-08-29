import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "45f8fe7c46e1811f1726ecc0c3d102f4d19fecd94ca385123a78cb75cbc3d7b0"
def certificateSHA256 : String := "3a9d45c815ba7915f28fdaba1c04ea935c5e63b3454a13d845d5eeef17b87348"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 642 := ![
  0,
  2,
  4,
  5,
  176,
  189,
  315,
  352,
  353,
  484,
  551,
  629,
  635,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (26, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (41, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (39, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (41, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (41, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (29, 1), (39, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (32, 1), (38, 1)] }]
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
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB6_5
