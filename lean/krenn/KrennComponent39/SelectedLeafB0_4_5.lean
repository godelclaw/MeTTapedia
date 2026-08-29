import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e75c0122fb2e860c3353485eb9c36639e68e7bb911fda8a97673852141bb20fe"
def certificateSHA256 : String := "e6932636302d6ced0fb261dc8f4bd801fa16ee8fc72ac2a9073a2520241d33d5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 670 := ![
  300,
  319,
  410,
  458,
  462,
  607,
  644,
  661,
  665,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(51, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (36, 1), (42, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (42, 1), (53, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (44, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (42, 1), (44, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (44, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(23, 1), (45, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(45, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (42, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (42, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1), (63, 1)] }],
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_4_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_4_5
