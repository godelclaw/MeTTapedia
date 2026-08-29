import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c1c23d9516ec23203cdc22a7aff7cb97c4b1750cde08f14ad43176f49e20a4d0"
def certificateSHA256 : String := "b728af6592c5002c81d26361ae40e9115bf19ee5695ce0c947b861c805cb8323"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 593 := ![
  6,
  40,
  48,
  208,
  250,
  261,
  363,
  366,
  376,
  377,
  489,
  586,
  587,
  589,
  591,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (36, 1), (46, 1), (56, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (36, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (36, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (36, 1), (46, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (56, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (24, 1), (36, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (36, 1), (46, 1), (56, 1), (58, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB5_1.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB5_1
