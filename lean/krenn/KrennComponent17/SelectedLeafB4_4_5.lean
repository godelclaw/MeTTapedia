import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "599ff6d80608c9f30057f9bdaa14e4c8c7ac0e57a9eaf22794a0f3ea278e8199"
def certificateSHA256 : String := "ce1d87ede3c2bb7002c6f12837c39cdcab6408a0bb2ef5fce88aa8f12c5c3984"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 611 := ![
  292,
  330,
  423,
  425,
  454,
  459,
  550,
  553,
  572,
  602,
  606,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(43, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 2), (45, 1), (59, 1), (62, 2)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (51, 1), (62, 2)] }, { coefficient := 1, powers := [(25, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (43, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (45, 1), (59, 1), (62, 2)] }, { coefficient := -1, powers := [(43, 1), (45, 1), (51, 1), (62, 2)] }, { coefficient := -1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (59, 1), (62, 2)] }, { coefficient := 1, powers := [(45, 1), (51, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (43, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 2), (43, 1), (45, 1), (59, 1), (62, 2)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (45, 1), (51, 1), (62, 2)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (43, 1), (51, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(43, 1), (51, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (43, 1), (51, 1), (53, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (51, 1), (53, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (33, 1), (43, 1), (51, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (43, 1), (51, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 2), (43, 1), (51, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (25, 1), (43, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (43, 1), (51, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (43, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (43, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (43, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 2), (43, 1), (45, 1), (59, 1), (62, 2)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (43, 1), (45, 1), (51, 1), (62, 2)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_4_5.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_4_5
