import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component44.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4f54bd893104a20a58faf79c10997a91498d611f2a8dd570c41916b9df71a47f"
def certificateSHA256 : String := "dd337d36259871ada24e650f13f3a70f5a9aa4f81600d3c78e0f0456859bf4bd"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 611 := ![
  1,
  3,
  4,
  5,
  6,
  7,
  151,
  153,
  208,
  212,
  221,
  362,
  363,
  364,
  365,
  391,
  553,
  607,
  608,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(0, 1), (2, 2), (21, 1), (38, 1), (48, 1), (53, 1), (58, 1), (60, 1), (61, 2)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (5, 1), (21, 1), (37, 1), (38, 1), (53, 1), (58, 1), (60, 1), (61, 2)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (48, 1), (53, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (8, 1), (26, 1), (34, 1), (38, 1), (48, 1), (58, 1), (60, 1), (61, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (40, 1), (58, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (26, 2), (40, 1), (58, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (34, 1), (38, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 2), (40, 1), (58, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (40, 1), (58, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (38, 1), (43, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (8, 1), (34, 1), (38, 1), (51, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 2), (38, 1), (46, 1), (48, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (37, 1), (38, 1), (46, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (46, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 2), (38, 1), (48, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (5, 1), (37, 1), (38, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (8, 1), (34, 1), (38, 1), (58, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (60, 1), (61, 2)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (40, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (40, 1), (59, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (38, 1), (58, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (14, 1), (38, 1), (58, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (40, 1), (58, 1), (60, 2)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (40, 1), (58, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (59, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (58, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (38, 1), (40, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (38, 1), (40, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 2), (21, 1), (38, 1), (46, 1), (48, 1), (53, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (21, 1), (37, 1), (38, 1), (46, 1), (53, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (8, 1), (26, 1), (34, 1), (38, 1), (48, 1), (51, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (43, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (26, 1), (46, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (38, 1), (40, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (38, 1), (40, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component44.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component44.SelectedLeafB5
