import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component13.SelectedLeafB4_0_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "43f53aa8d773d037663afcce5c26e40a73bf601e8c89a92d6f0523c0ac0aa343"
def certificateSHA256 : String := "3cdeb83475f81691c4f8e3160e777ed360bb49c2dd2db5b20d215e395eb1a411"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 614 := ![
  17,
  19,
  170,
  188,
  189,
  284,
  325,
  360,
  361,
  376,
  480,
  483,
  525,
  604,
  607,
  609,
  610,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (41, 1)] }, { coefficient := 1, powers := [(41, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (27, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (41, 1), (50, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component13.SelectedLeafB4_0_6.selectedHasNoCommonZero

end Krenn.Component13.SelectedLeafB4_0_6
