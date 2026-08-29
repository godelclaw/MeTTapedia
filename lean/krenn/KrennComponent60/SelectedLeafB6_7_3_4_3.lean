import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_7_3_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b38e383848d33d282557976a21f1a7587beb6b1e22b8af5d01ebe71c5bfae10c"
def certificateSHA256 : String := "0fea77fee83859531b2193b1547f46ad475b2a67e1b703d80bf9c7038bb16f84"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 671 := ![
  18,
  20,
  22,
  43,
  143,
  164,
  168,
  172,
  177,
  198,
  301,
  302,
  308,
  331,
  436,
  443,
  556,
  578,
  579,
  593,
  655,
  658,
  659,
  663,
  664,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(18, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 71) := ![
  [{ coefficient := -2, powers := [(24, 1), (25, 1), (40, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 1), (50, 1), (51, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (52, 1), (57, 1), (63, 1), (67, 1)] }, { coefficient := -2, powers := [(24, 1), (54, 1), (57, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (53, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (57, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (51, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 2, powers := [(0, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(20, 1), (51, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 2, powers := [(20, 1), (52, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 2, powers := [(25, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(52, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (40, 1), (57, 1)] }, { coefficient := -2, powers := [(24, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (40, 1), (50, 1), (57, 1)] }, { coefficient := 2, powers := [(24, 1), (50, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (24, 1), (57, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (57, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (51, 1), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(20, 1), (51, 1), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(20, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (41, 1), (51, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(0, 1), (47, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(20, 1), (41, 1), (51, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 2, powers := [(20, 1), (41, 1), (56, 2), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(25, 1), (47, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(38, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (57, 2), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 2), (67, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (57, 1), (67, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (40, 1), (50, 1), (57, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (50, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (24, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (32, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (24, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (24, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (48, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (39, 1), (41, 1), (57, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1), (50, 1), (57, 1), (67, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_7_3_4_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_7_3_4_3
