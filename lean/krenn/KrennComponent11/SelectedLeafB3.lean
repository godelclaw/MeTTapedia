import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "56f49441a87f3a4973db777b00f9838911bc0e427114d5baabc7fbae6cefccb6"
def certificateSHA256 : String := "8ee84b7ca2bced836e85a4303954e949b03a3a345a71c9c8df74ac33e7478f0f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 666 := ![
  3,
  6,
  15,
  16,
  184,
  186,
  192,
  323,
  328,
  330,
  350,
  453,
  485,
  662,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (33, 1), (37, 1), (49, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 2), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1), (37, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (37, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (37, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (37, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (42, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (37, 1), (42, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (37, 1), (46, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (37, 2), (57, 1), (59, 2)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (33, 1), (37, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB3
