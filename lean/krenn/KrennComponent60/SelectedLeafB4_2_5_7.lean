import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "38cd4fbe95ed8c9d4c0ce38d3202f23c1fec6f43e19f5fc7800837cf4de252d7"
def certificateSHA256 : String := "85a2da109f719005f921fc379c635583cd242bd4d667a558d54094e76d4d6be0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 668 := ![
  22,
  25,
  145,
  168,
  172,
  177,
  194,
  237,
  295,
  302,
  310,
  383,
  404,
  436,
  443,
  491,
  556,
  579,
  655,
  658,
  660,
  661,
  663,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (35, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (54, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (48, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (57, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (52, 1), (53, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (46, 1), (53, 1), (54, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (48, 1), (52, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (29, 1), (32, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (35, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (46, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (50, 1), (51, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_5_7.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_5_7
