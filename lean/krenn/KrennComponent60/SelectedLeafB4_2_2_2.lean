import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e0fda5050de8dffb8b16abfe7c5c46ab771fea940323a06042fe3eaae114f6c6"
def certificateSHA256 : String := "8362c91d572ef66803a5159e1b2c00d826365c7ba0b55ca926f9acd636dc9928"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 668 := ![
  22,
  165,
  172,
  301,
  302,
  404,
  436,
  443,
  556,
  655,
  658,
  661,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1), (50, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_2_2.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_2_2
