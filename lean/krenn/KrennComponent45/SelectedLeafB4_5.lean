import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component45.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d5929b0e1c6e8cb0f70c2e2910dd732f4d0723df3c1a5f4fe6a0c1e553336cc6"
def certificateSHA256 : String := "7a2251266b2c6a50a48426a68556f35dd2d72b6bc30aa5e99a84a43829346743"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 566 := ![
  33,
  40,
  200,
  201,
  231,
  360,
  379,
  380,
  386,
  412,
  491,
  492,
  559,
  560,
  562,
  563,
  564,
  565
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (49, 1), (58, 1)] }, { coefficient := -2, powers := [(24, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (45, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (46, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (45, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (45, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(40, 1), (42, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (49, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (33, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (25, 1), (26, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (30, 1), (46, 1), (57, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component45.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component45.SelectedLeafB4_5
