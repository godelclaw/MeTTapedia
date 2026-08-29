import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a1be745ea2b7a5d931748c0962e819a09313d1f55782dd3123cfc826fa71f8b1"
def certificateSHA256 : String := "c115278c7402e266ab11c91455725aee847fd29a17dca92e0cd051db59c4cd1f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 673 := ![
  16,
  22,
  28,
  29,
  30,
  31,
  190,
  191,
  261,
  277,
  300,
  301,
  314,
  350,
  430,
  440,
  451,
  463,
  465,
  482,
  581,
  625,
  645,
  660,
  661,
  663,
  666,
  667,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (57, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (37, 1), (59, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (28, 1), (47, 1), (52, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (28, 1), (42, 1), (52, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (59, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (59, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(21, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(26, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (35, 1), (53, 1), (59, 1), (65, 1), (69, 1), (70, 1)] }, { coefficient := 1, powers := [(28, 1), (35, 1), (59, 1), (65, 1), (69, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (54, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (19, 1), (54, 1), (59, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (54, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (28, 1), (52, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (27, 1), (49, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (49, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (23, 1), (52, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (49, 1), (59, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (49, 1), (57, 1), (59, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (23, 1), (49, 1), (57, 1), (59, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (49, 1), (59, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (54, 1), (59, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (49, 1), (59, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (54, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (59, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (59, 1), (65, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (28, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (53, 1), (59, 1), (65, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (59, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (57, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (35, 1), (59, 1), (70, 1)] }, { coefficient := -1, powers := [(35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (37, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (59, 2)] }, { coefficient := -1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (23, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (35, 1), (53, 1), (59, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (46, 1), (49, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (47, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (28, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (19, 1), (42, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (23, 1), (46, 1), (49, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (24, 1), (47, 1), (49, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (21, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (26, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (28, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (28, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (27, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (23, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (35, 1), (41, 1), (53, 1), (59, 1), (65, 1), (70, 1)] }, { coefficient := -1, powers := [(28, 1), (35, 1), (41, 1), (59, 1), (65, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (35, 1), (56, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_7_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_7_7
