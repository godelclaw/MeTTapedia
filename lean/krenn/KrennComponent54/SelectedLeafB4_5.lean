import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component54.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d5784a3327fddffd3c2530826f782af13fd50f59790e30440008e9f35c34c33e"
def certificateSHA256 : String := "7d856b86bd542a9e00cbc374a986300ccb88556737081aecbf13e98b85933a49"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 645 := ![
  9,
  11,
  22,
  186,
  203,
  204,
  235,
  288,
  310,
  351,
  352,
  357,
  359,
  360,
  473,
  560,
  579,
  638,
  641,
  642,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (27, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (33, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 2), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (36, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (25, 1), (33, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 2), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (14, 1), (33, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (39, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (42, 1), (57, 2), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (48, 1), (54, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (42, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (33, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (27, 1), (33, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (27, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component54.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component54.SelectedLeafB4_5
