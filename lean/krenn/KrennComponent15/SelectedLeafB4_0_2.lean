import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB4_0_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7e7e9157098bfd65d7a1a82aea1a17c0062438964d5a827e82570f2f923e6eaf"
def certificateSHA256 : String := "26625e0026f25335768a451157013350b0188f43beb5dfb9d6379f260707f19e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 595 := ![
  215,
  226,
  232,
  234,
  236,
  336,
  365,
  366,
  367,
  368,
  376,
  519,
  527,
  585,
  588,
  590,
  591,
  594
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(40, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 59) := ![
  [{ coefficient := -2, powers := [(5, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (40, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (21, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (26, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (21, 1), (40, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (22, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 2, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB4_0_2.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB4_0_2
