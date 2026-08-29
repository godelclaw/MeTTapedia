import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cf798282bdb58e1aa00647a702e422dfc774eb42952954b3580a6f55bbec4a86"
def certificateSHA256 : String := "90ffa32861b3babf3c436a82eb73c22ba9f056370c0f4330733f2fa0bbb2a936"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 593 := ![
  3,
  33,
  40,
  208,
  247,
  250,
  287,
  354,
  363,
  366,
  376,
  377,
  404,
  528,
  586,
  587,
  589,
  590,
  591,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (41, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (41, 1), (46, 1), (58, 1), (61, 2)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (41, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (41, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (41, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (41, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (41, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(41, 2), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (41, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (24, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (41, 1), (46, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB6_5
