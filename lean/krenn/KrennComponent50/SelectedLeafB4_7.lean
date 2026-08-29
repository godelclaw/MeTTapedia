import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component50.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c25ff0af2250fc6d1fb6ceb078a7c2dbb0ca4ab6b17f488798e4da8a19150585"
def certificateSHA256 : String := "b97d6ecbe9104d8423d725dc8039acfe7652c6df8e4ea15a639dbcf4843d40aa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 641 := ![
  2,
  3,
  26,
  30,
  58,
  60,
  162,
  166,
  168,
  175,
  228,
  243,
  348,
  349,
  359,
  362,
  363,
  443,
  556,
  582,
  627,
  634,
  635,
  637,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := -2, powers := [(5, 2), (20, 1), (30, 1), (33, 1), (42, 1), (44, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (8, 1), (20, 1), (24, 1), (33, 1), (42, 1), (44, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (33, 2), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (44, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (56, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (20, 1), (33, 2), (42, 1), (44, 1), (47, 1), (56, 1), (60, 1), (63, 2)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (20, 1), (30, 1), (33, 1), (42, 1), (44, 1), (50, 2), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (41, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (44, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (47, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (42, 1), (50, 2), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 2), (20, 1), (33, 1), (42, 1), (44, 1), (53, 1), (56, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (53, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (8, 1), (20, 1), (33, 2), (42, 1), (44, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(8, 1), (33, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (42, 1), (44, 1), (52, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(42, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (42, 1), (44, 1), (56, 2), (62, 1)] }, { coefficient := -2, powers := [(42, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (44, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (20, 1), (33, 1), (42, 1), (44, 1), (56, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (8, 1), (20, 1), (33, 1), (42, 1), (44, 1), (56, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (20, 1), (33, 1), (42, 1), (44, 1), (53, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(8, 1), (59, 1)] }, { coefficient := -2, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (42, 1), (44, 1), (53, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (42, 1), (44, 1), (53, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(6, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 1), (36, 1), (42, 2), (44, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (36, 1), (42, 1), (44, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (25, 1), (30, 1), (33, 1), (42, 1), (44, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (30, 1), (33, 1), (42, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(25, 1), (30, 1), (42, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (19, 1), (20, 1), (33, 1), (42, 1), (44, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (20, 1), (33, 1), (42, 1), (44, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(14, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 1), (30, 1), (33, 1), (42, 1), (44, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(30, 1), (42, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (42, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(42, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (42, 1), (44, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(5, 1), (8, 1), (20, 1), (33, 2), (42, 1), (44, 1), (47, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (42, 1), (44, 1), (47, 1), (53, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (39, 1), (42, 1), (44, 1), (56, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (41, 1), (42, 1), (44, 1), (56, 2), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (42, 2), (44, 1), (56, 2), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (42, 1), (44, 1), (50, 1), (56, 2), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (36, 1), (42, 2), (44, 1), (53, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (36, 1), (42, 1), (44, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(39, 1), (59, 1)] }, { coefficient := -2, powers := [(41, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(42, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(42, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (6, 1), (20, 1), (33, 1), (36, 1), (42, 1), (44, 1), (53, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (20, 1), (33, 1), (36, 1), (42, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (44, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 2), (20, 1), (33, 2), (44, 1), (56, 2)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (20, 1), (25, 1), (33, 2), (42, 1), (44, 1), (47, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (20, 1), (30, 1), (36, 1), (42, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (20, 1), (25, 1), (30, 1), (33, 1), (42, 1), (44, 1), (50, 2), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (25, 1), (33, 1), (41, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (25, 1), (33, 1), (44, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (33, 1), (47, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (30, 1), (42, 1), (50, 2), (62, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component50.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component50.SelectedLeafB4_7
