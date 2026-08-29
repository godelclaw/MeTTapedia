import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component45.SelectedLeafB6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "977624a9db6ee48800223656a2b0defb88fa6009f472baad0bc32eddd0aa6b31"
def certificateSHA256 : String := "11304409bdf1e9c30c15d2bd263d75b1ce78c16fc5b92828afead78fc7b0ea82"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 566 := ![
  4,
  32,
  200,
  201,
  237,
  249,
  284,
  286,
  360,
  378,
  379,
  380,
  386,
  440,
  484,
  513,
  559,
  562,
  564,
  565
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 59) := ![
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (33, 1), (45, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }]
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
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component45.SelectedLeafB6_0.selectedHasNoCommonZero

end Krenn.Component45.SelectedLeafB6_0
