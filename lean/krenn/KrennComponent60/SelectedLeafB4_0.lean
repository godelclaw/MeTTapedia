import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ffb49122a686e3467f5d65ffa6352b9a815795abd577cf39de7de963c09426f0"
def certificateSHA256 : String := "2f8676b3daa8328a69518e1226f7e58dd17a57e9adf42144a967c6cb581e6db4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 662 := ![
  22,
  25,
  55,
  56,
  143,
  145,
  147,
  172,
  173,
  178,
  179,
  194,
  237,
  292,
  301,
  302,
  308,
  310,
  383,
  404,
  422,
  433,
  436,
  442,
  443,
  460,
  556,
  578,
  608,
  655,
  656,
  658,
  660,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (43, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (43, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (45, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (43, 1), (45, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (43, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (43, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (43, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(24, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(20, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (43, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (45, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 2), (32, 1), (43, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (32, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (32, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_0.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_0
