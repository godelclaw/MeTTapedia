import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_5_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0d6b06b87f618d09f43c24b9bc3efceeaff4f08e54ddeba7d08ed1e4b7e0af07"
def certificateSHA256 : String := "bde15a0aab157209eb7a4711a733b44a8694baa3cd8530f79426a2e52de22ef7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 9 → Fin 670 := ![
  319,
  413,
  452,
  462,
  581,
  607,
  665,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 9 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 9 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (51, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (42, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (42, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (45, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 9,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_5_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_5_5
