import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_6_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c95cc3ba3bbedb330bf7ef924d8be8cb71e0ede0d5fe7ec85edcec5eacd85c92"
def certificateSHA256 : String := "2e9df4d5eddc77360dafccc6bcafcfc2fe27ecffa28b0eea54fc91a7817b2602"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 674 := ![
  10,
  13,
  18,
  23,
  28,
  29,
  170,
  171,
  302,
  316,
  408,
  436,
  440,
  445,
  447,
  448,
  454,
  478,
  620,
  661,
  667,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(31, 1), (50, 1), (68, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (31, 1), (38, 1), (42, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (38, 1), (47, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (38, 1), (42, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (38, 1), (47, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (38, 1), (54, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (49, 1), (61, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (54, 1), (61, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (31, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (22, 1), (31, 1), (38, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (22, 1), (31, 1), (38, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (27, 1), (38, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (27, 1), (38, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (38, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (38, 1), (49, 1), (61, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_6_6_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_6_6_3
