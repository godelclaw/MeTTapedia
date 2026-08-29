import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_6_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e43e7284fad805143b00f24024204453e96a8dfe2bd32507f16887dc96238bc1"
def certificateSHA256 : String := "5f94a939eee2762a76a69c42a61bf96d154676540fc2479d616073de45fb5659"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 668 := ![
  151,
  152,
  153,
  211,
  292,
  304,
  312,
  422,
  463,
  582,
  583,
  608,
  659,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1), (63, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (57, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(40, 1), (63, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (40, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (40, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (45, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (51, 1), (56, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (40, 1), (43, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (45, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (56, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (26, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (43, 1), (45, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (43, 1), (51, 1), (56, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (40, 1), (43, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (46, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (40, 1), (43, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (46, 1), (53, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (40, 1), (56, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (40, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (40, 1), (56, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (40, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (40, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(39, 1), (63, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_6_3_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_6_3_3
