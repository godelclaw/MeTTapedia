import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "27b79e764c5c9eccca0e6cc30c8cb5c865607168edebb7cd6b15bec87f7cf587"
def certificateSHA256 : String := "22f749674106d5fcfd9cda07b9db4f8f68a25d9fe8bd40f29484c2bc2d5d7901"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 665 := ![
  22,
  25,
  143,
  169,
  172,
  173,
  177,
  178,
  194,
  236,
  292,
  294,
  301,
  302,
  308,
  310,
  314,
  327,
  383,
  404,
  423,
  443,
  459,
  466,
  556,
  578,
  579,
  599,
  609,
  621,
  655,
  656,
  658,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (50, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (25, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 2), (35, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (35, 1), (45, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (35, 1), (47, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(50, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (35, 1), (45, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (47, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (35, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (47, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 2), (35, 1), (45, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (35, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (35, 1), (47, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (50, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 2), (25, 1), (35, 1), (45, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (25, 1), (35, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (25, 1), (35, 1), (47, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (25, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (25, 1), (35, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (35, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (20, 1), (24, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (24, 1), (25, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (48, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_1_5.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_1_5
