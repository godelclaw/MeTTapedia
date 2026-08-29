import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fb56b3c990e6f0502e42e70f6b46a4fb40567535ec63060b74b3749f3c1e8280"
def certificateSHA256 : String := "dea041d8c96c4b0b6e69bd7fc2a17963fe5052ede0a44393b0d043bc1f911e88"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 668 := ![
  25,
  27,
  44,
  57,
  86,
  164,
  169,
  172,
  177,
  179,
  194,
  301,
  302,
  443,
  506,
  578,
  579,
  643,
  655,
  658,
  660,
  661,
  662,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := -2, powers := [(18, 1), (25, 1), (29, 1), (48, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (29, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (38, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (38, 1), (40, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (38, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (38, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (54, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(29, 1), (48, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (51, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (51, 1), (54, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (48, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (51, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (35, 1), (38, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (38, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (40, 1), (51, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (38, 1), (51, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(54, 1)] }],
  [{ coefficient := 2, powers := [(48, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (29, 1), (35, 1), (38, 1), (40, 1), (51, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (40, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (35, 1), (38, 1), (51, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (38, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (35, 1), (38, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(38, 1), (60, 1)] }, { coefficient := -2, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (35, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (29, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (24, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (51, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (40, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (12, 1), (35, 1), (38, 1), (40, 1), (51, 2), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (20, 1), (35, 1), (38, 1), (40, 1), (51, 2), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (20, 1), (35, 1), (38, 1), (40, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (40, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (45, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (51, 2), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (35, 1), (38, 1), (51, 2), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (35, 1), (38, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (35, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1), (40, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1), (45, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (25, 1), (29, 1), (48, 1), (50, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (29, 1), (50, 1), (65, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_6_5.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_6_5
