import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component52.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8c7195100b5ddbdc3447c1418cb6b517349b0f5e4e236cc84cffc96ba0ea5209"
def certificateSHA256 : String := "691667f86385c9a652bc49dcfc9147d5453cb0b9c405efa38a7d45e9b5924ca6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 637 := ![
  1,
  4,
  5,
  6,
  8,
  9,
  11,
  162,
  164,
  203,
  207,
  208,
  353,
  354,
  356,
  357,
  487,
  581,
  633,
  634,
  636
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(0, 1), (2, 2), (19, 1), (36, 1), (47, 1), (53, 1), (58, 1), (60, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (5, 1), (19, 1), (35, 1), (36, 1), (53, 1), (58, 1), (60, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (47, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (8, 1), (24, 1), (32, 1), (36, 1), (47, 1), (58, 1), (60, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (46, 1), (59, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (38, 1), (58, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (24, 2), (38, 1), (58, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (32, 1), (36, 1), (56, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 2), (38, 1), (58, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (38, 1), (58, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (35, 1), (36, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (8, 1), (32, 1), (36, 1), (50, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 2), (36, 1), (44, 1), (47, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (35, 1), (36, 1), (44, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (44, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 2), (36, 1), (47, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (5, 1), (35, 1), (36, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (8, 1), (32, 1), (36, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (60, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (59, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (18, 1), (36, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (13, 1), (36, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (58, 1), (60, 2)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (58, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (36, 1), (59, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (36, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (36, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 2), (19, 1), (36, 1), (44, 1), (47, 1), (53, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (19, 1), (35, 1), (36, 1), (44, 1), (53, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (8, 1), (24, 1), (32, 1), (36, 1), (47, 1), (50, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (36, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (44, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (36, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (36, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component52.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component52.SelectedLeafB7
