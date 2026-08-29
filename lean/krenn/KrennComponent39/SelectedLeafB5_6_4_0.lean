import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_4_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2c99905800fddedc4286dc3ab37783e549707049132f49ca9ea76734b0d0c1ad"
def certificateSHA256 : String := "328a4bd873d02fa5c84f01243874e73d706ca8da733f6a87c379f5d50ebad604"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 13 → Fin 673 := ![
  396,
  416,
  422,
  439,
  441,
  482,
  644,
  649,
  661,
  663,
  665,
  668,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 13 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 13 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (35, 1), (44, 1), (51, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (36, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (51, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (36, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (51, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (35, 1), (44, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (44, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (27, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (44, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (35, 1), (59, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (59, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(39, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (35, 1), (39, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (35, 1), (44, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (44, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (35, 1), (39, 1), (44, 1), (51, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (35, 1), (44, 2), (51, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (36, 1), (39, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (36, 1), (44, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (39, 1), (44, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (39, 1), (51, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (44, 2), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (44, 1), (51, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (36, 1), (39, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (36, 1), (44, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (26, 1), (39, 1), (51, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (26, 1), (44, 1), (51, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (35, 1), (39, 1), (44, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (35, 1), (44, 2), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (39, 1), (44, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (39, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (44, 2), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (44, 1), (61, 1), (62, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 13,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_4_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_4_0
