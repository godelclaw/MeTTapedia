import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_2_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d85b707782dde01af8041b4b4f50397e0829d1f63533de5e0b4bd7885e523e22"
def certificateSHA256 : String := "24dad79c0d55b241f684b158d3b18f1409b8e5f9aeabdcc9834f6e7423ea3e8c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 675 := ![
  13,
  15,
  19,
  253,
  272,
  298,
  299,
  305,
  307,
  318,
  320,
  325,
  448,
  451,
  465,
  583,
  596,
  609,
  662,
  663,
  665,
  668,
  670,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (36, 1), (38, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (58, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (52, 2), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (52, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (35, 1), (38, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1), (45, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (36, 1), (38, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (35, 1), (38, 1), (45, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (45, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (36, 1), (38, 1), (55, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (28, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (35, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (43, 1), (52, 2), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (43, 1), (52, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (35, 1), (38, 1), (43, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (43, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (38, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (35, 1), (36, 1), (38, 1), (60, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_2_3_1.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_2_3_1
