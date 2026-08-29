import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB1_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dfe61074c963172b777aa267bee39cb6f0b7053d95de62cbcd40ae5f4bec8e6b"
def certificateSHA256 : String := "c0b21ce9a6c7f5419b16f5df201aa7060066d2b51f48de375888a41359fee10a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 611 := ![
  206,
  330,
  410,
  432,
  445,
  454,
  459,
  481,
  506,
  549,
  550,
  572,
  602,
  604,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (40, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (44, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (40, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (44, 1), (55, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (55, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 2), (28, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (55, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (55, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (55, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (55, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (44, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (50, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(50, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(55, 1), (63, 1)] }],
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB1_6_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB1_6_3
