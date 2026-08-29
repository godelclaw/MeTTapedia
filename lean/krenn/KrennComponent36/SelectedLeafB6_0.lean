import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a6b35ebeea16787a3a4e2f6e797c8f4dc183ea45cf2b67721e0da919bf143e85"
def certificateSHA256 : String := "46fdd2c3395fd87035d4e5455a1ac0db31e881ca04a51bc9e5473532f7019caa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 669 := ![
  0,
  1,
  2,
  3,
  10,
  13,
  15,
  19,
  160,
  272,
  305,
  307,
  379,
  443,
  448,
  451,
  562,
  583,
  612,
  662,
  664,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (29, 1), (43, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (29, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (29, 1), (43, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (29, 1), (45, 1), (63, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (29, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (29, 1), (45, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (45, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (32, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (45, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (43, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (29, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (45, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (29, 1), (43, 1), (45, 1), (47, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (29, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (29, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (29, 1), (43, 1), (45, 1), (47, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (29, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (32, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 2), (32, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (45, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB6_0.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB6_0
