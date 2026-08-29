import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component48.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4f1b215ef6ab0a0006a030a81ca6228d84ee4a5877405ec7b366cb48979335b8"
def certificateSHA256 : String := "756309ffb834e83cab39549d8554cc54163ffcbc8955060d6f2d30883ddee866"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 641 := ![
  24,
  30,
  161,
  162,
  190,
  348,
  359,
  360,
  385,
  464,
  466,
  478,
  634,
  635,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(24, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (48, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := -1, powers := [(40, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(42, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (33, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (26, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (48, 1), (60, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component48.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component48.SelectedLeafB6_5
