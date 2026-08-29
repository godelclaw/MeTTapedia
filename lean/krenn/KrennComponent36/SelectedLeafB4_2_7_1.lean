import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_2_7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3b3d14fc7e7a8354becfe4d46286e9210e2b5808c99beeeb83484d1cb33767dd"
def certificateSHA256 : String := "6e43e72e102c6a8adfd33d8718c8d992814e6723070fa6be94a743018446e892"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 675 := ![
  15,
  19,
  256,
  272,
  299,
  305,
  307,
  325,
  448,
  451,
  596,
  662,
  665,
  668,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(23, 1), (46, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (53, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (58, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (52, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 2), (66, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(48, 1), (55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (44, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (44, 1), (47, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (48, 1), (52, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1), (44, 1), (58, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (40, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (38, 1), (40, 1), (58, 1), (66, 1)] }]
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

#print axioms Krenn.Component36.SelectedLeafB4_2_7_1.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_2_7_1
