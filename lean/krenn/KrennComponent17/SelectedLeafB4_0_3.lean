import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_0_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6fc1f910c7e20c2e8b73d8cf46267b58b709887b308dca5272d1628f2c29a615"
def certificateSHA256 : String := "61156c81252b70925b47ce0b2b6f61e6fcf8fea7d92577e63abad06bbfa8c8ea"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 611 := ![
  5,
  7,
  14,
  17,
  18,
  32,
  60,
  183,
  190,
  202,
  206,
  207,
  210,
  285,
  306,
  307,
  311,
  323,
  325,
  327,
  330,
  415,
  423,
  425,
  430,
  434,
  436,
  441,
  454,
  459,
  505,
  541,
  572,
  601,
  602,
  604,
  606,
  607,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (25, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (25, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (25, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (29, 1), (45, 1), (47, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(25, 1), (29, 1), (36, 1), (45, 1), (47, 1), (57, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (20, 1), (25, 1), (29, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 2), (45, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (29, 1), (36, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (25, 1), (38, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 2), (36, 1), (45, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (36, 1), (45, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (38, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (25, 2), (45, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 2), (36, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (25, 1), (45, 1), (47, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (43, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (36, 1), (45, 1), (47, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (45, 1), (55, 1), (57, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (43, 1), (45, 1), (50, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (45, 1), (47, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (25, 2), (43, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 2), (36, 1), (43, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (45, 2), (52, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (45, 1), (52, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (36, 1), (45, 1), (52, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (43, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (36, 1), (43, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (51, 2), (61, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (29, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (29, 1), (36, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (25, 1), (29, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (29, 1), (36, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(25, 1), (29, 1), (36, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (23, 1), (25, 1), (45, 1), (52, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (25, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (27, 1), (45, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (45, 1), (52, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (51, 2), (61, 2)] }],
  [{ coefficient := -1, powers := [(45, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (36, 1), (45, 1), (52, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (45, 1), (47, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (36, 1), (45, 1), (47, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (45, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (38, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (36, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (51, 1), (61, 2)] }, { coefficient := 1, powers := [(50, 1), (61, 1)] }, { coefficient := 1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (36, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(43, 1), (51, 1), (61, 2)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (29, 1), (45, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (29, 1), (36, 1), (45, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (25, 1), (36, 1), (45, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(43, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (38, 1), (45, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(25, 1), (36, 1), (45, 1), (47, 1), (52, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (50, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (55, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (51, 1), (55, 1), (61, 2)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (19, 1), (23, 1), (25, 1), (45, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (23, 1), (24, 1), (25, 1), (45, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (43, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (43, 2), (51, 2), (61, 2)] }, { coefficient := 1, powers := [(25, 1), (43, 2), (51, 1), (61, 2)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (25, 1), (29, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (25, 1), (29, 1), (36, 1), (45, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (45, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (35, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (25, 1), (35, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (27, 1), (43, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (29, 1), (36, 1), (45, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (32, 1), (45, 1), (55, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_0_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_0_3
