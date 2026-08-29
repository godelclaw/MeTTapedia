import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c899d14db8f9c2e991d35d007d96b7c374cb53bd8e1a286ec830c00680534b21"
def certificateSHA256 : String := "841a9baa568b6b47a52c3316f7319ab9c1714c1459a1fbe1d904fc65adb0ad3c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 664 := ![
  0,
  1,
  3,
  4,
  14,
  144,
  180,
  183,
  294,
  310,
  311,
  340,
  349,
  413,
  431,
  440,
  449,
  466,
  472,
  484,
  485,
  487,
  503,
  562,
  566,
  581,
  628,
  645,
  649,
  657,
  658,
  659,
  660,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (29, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (26, 1), (29, 1), (42, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (42, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (42, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (42, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (26, 1), (42, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (42, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (26, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (42, 1)] }, { coefficient := -1, powers := [(28, 1), (42, 1)] }, { coefficient := -1, powers := [(29, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (41, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (29, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (29, 1), (42, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(37, 1), (42, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(42, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (29, 1), (42, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (26, 1), (29, 1), (42, 1), (44, 1)] }]
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
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB2_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB2_3
