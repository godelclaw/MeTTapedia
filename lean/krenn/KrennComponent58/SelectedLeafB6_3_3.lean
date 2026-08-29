import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB6_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "df8a02ea3a2e3adb9a64cd6e286281cade47731f5c343ab661b9d8fa58fabfa9"
def certificateSHA256 : String := "869ee53544f8267391311613fa688c6eaa1ef5e305bb94b2dece80eae6df79c7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 622 := ![
  30,
  31,
  44,
  192,
  335,
  460,
  488,
  561,
  562,
  565,
  582,
  584,
  613,
  618,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(35, 1), (45, 1), (48, 1), (54, 1), (55, 1), (57, 1), (62, 1), (64, 2)] }, { coefficient := -1, powers := [(35, 1), (45, 1), (51, 1), (55, 1), (57, 1), (62, 1), (64, 2)] }, { coefficient := 1, powers := [(35, 1), (46, 1), (52, 1), (54, 1), (57, 1), (62, 1), (64, 2)] }, { coefficient := 1, powers := [(45, 1), (48, 1), (50, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (42, 1), (52, 1), (54, 1), (57, 1), (62, 1), (64, 2)] }, { coefficient := 1, powers := [(35, 1), (48, 1), (54, 1), (55, 1), (57, 1), (62, 1), (64, 2)] }, { coefficient := -1, powers := [(35, 1), (48, 1), (54, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (51, 1), (55, 1), (57, 1), (62, 1), (64, 2)] }, { coefficient := -1, powers := [(48, 1), (50, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (54, 1), (58, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (46, 1), (54, 1), (57, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (45, 1), (55, 1), (57, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (54, 1), (57, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (55, 1), (57, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (50, 1)] }, { coefficient := -1, powers := [(35, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(25, 1), (50, 1)] }, { coefficient := 1, powers := [(35, 1), (55, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (45, 1), (48, 1), (54, 1), (55, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (45, 1), (51, 1), (55, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (35, 1), (46, 1), (52, 1), (54, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (45, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (35, 1), (42, 1), (52, 1), (54, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (48, 1), (54, 1), (55, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (51, 1), (55, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(35, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB6_3_3.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB6_3_3
