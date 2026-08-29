import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB4_6_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f977fd3282dbb1d8912751690ca0493e5560e57df08060414a4845ee21915cc1"
def certificateSHA256 : String := "3c4b3dd2b81fcc1b941765560d8a0e85747fcd8997cc25c637b5125113696f9b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 674 := ![
  5,
  6,
  10,
  18,
  23,
  28,
  300,
  301,
  316,
  366,
  440,
  445,
  454,
  497,
  518,
  523,
  608,
  609,
  660,
  661,
  663,
  664,
  667,
  669,
  670,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(4, 1), (37, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (37, 1), (42, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (37, 1), (47, 2), (53, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (37, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (37, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (37, 1), (47, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (23, 1), (37, 1), (42, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (23, 1), (37, 1), (47, 1), (55, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (37, 1), (49, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(4, 1), (37, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (22, 1), (23, 1), (37, 1), (42, 1), (47, 1), (55, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (22, 1), (23, 1), (37, 1), (47, 2), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (22, 1), (28, 1), (37, 1), (42, 1), (47, 2), (55, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (22, 1), (28, 1), (37, 1), (47, 3), (55, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (23, 1), (37, 1), (47, 1), (49, 1), (55, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (28, 1), (37, 1), (47, 2), (49, 1), (55, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (37, 1), (47, 2), (49, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (61, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (23, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (28, 1), (37, 1), (47, 2), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (23, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (22, 1), (23, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (22, 1), (28, 1), (37, 1), (47, 2), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (37, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (37, 1), (47, 2), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (37, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (39, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (42, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (42, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (47, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (11, 1), (33, 1), (37, 1), (47, 2), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (22, 1), (23, 1), (37, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (22, 1), (23, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (23, 1), (37, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (19, 1), (22, 1), (23, 1), (37, 1), (42, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (19, 1), (22, 1), (23, 1), (37, 1), (47, 2), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (19, 1), (22, 1), (28, 1), (37, 1), (42, 1), (47, 2), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (19, 1), (22, 1), (28, 1), (37, 1), (47, 3), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (19, 1), (23, 1), (37, 1), (47, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (19, 1), (28, 1), (37, 1), (47, 2), (49, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB4_6_6_6.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB4_6_6_6
