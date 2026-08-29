import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component53.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "582ee20559d0e2949203d6d9d5c95125f0b62780cae7a3b21933585f145aa6c1"
def certificateSHA256 : String := "7db89966008474d2717ccd2c544f325de39543723edfce33d2bbdcabc06339ed"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 640 := ![
  4,
  20,
  21,
  27,
  29,
  40,
  221,
  359,
  360,
  364,
  463,
  474,
  491,
  636,
  637,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(34, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (38, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (34, 1), (38, 1), (51, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (37, 1), (38, 1), (51, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (34, 1), (38, 1), (48, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (38, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (43, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (48, 1), (54, 1), (59, 1)] }],
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component53.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component53.SelectedLeafB5
