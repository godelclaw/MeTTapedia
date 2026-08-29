import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB6_3_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "52688355256cb75dbdfe5eb92826989d89d9321d519b8760475e9d5fd6eae75f"
def certificateSHA256 : String := "f6a4c63045fa104af7ce23857447e9882c88c0cc2c057d41237baaf521e0e7b9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 674 := ![
  303,
  315,
  317,
  414,
  434,
  447,
  582,
  667,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (46, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (46, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (40, 1), (44, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (42, 1), (44, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (44, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(44, 1), (64, 1)] }, { coefficient := 1, powers := [(64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1), (42, 1), (44, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (40, 1), (42, 1), (44, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (40, 1), (44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [(46, 1), (49, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB6_3_1_4.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB6_3_1_4
