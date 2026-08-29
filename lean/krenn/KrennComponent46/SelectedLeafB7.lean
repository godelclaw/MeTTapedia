import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component46.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7780607fdc755a9f45d7565feb9dbdd32302ab71690a3efa33ed2b058bcfc087"
def certificateSHA256 : String := "47c096c0f99360a6e0bb769013e6cca71f1f265341137ccb5bc34e426cd2ca19"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 643 := ![
  5,
  12,
  15,
  21,
  23,
  24,
  37,
  40,
  165,
  197,
  220,
  350,
  352,
  357,
  361,
  362,
  365,
  434,
  466,
  494,
  639,
  640,
  641,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(26, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(34, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (38, 1), (46, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1), (56, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (49, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (38, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (38, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (34, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (49, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (38, 1), (53, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (27, 1), (38, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (38, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (43, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (49, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (49, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component46.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component46.SelectedLeafB7
