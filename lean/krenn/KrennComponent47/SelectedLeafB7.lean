import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0208397b07293e96c00f494bae49de67b8a1f5c2618e4d7a95435bd3dc040df9"
def certificateSHA256 : String := "8310802fc12bfbe4e1619a246e730a1533d581b6d79908d9a12eef6c924794b7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 590 := ![
  6,
  18,
  25,
  32,
  34,
  35,
  48,
  51,
  211,
  240,
  261,
  363,
  366,
  370,
  376,
  377,
  380,
  449,
  470,
  489,
  586,
  587,
  588,
  589
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (36, 1), (43, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (53, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (36, 1), (46, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (36, 1), (53, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (32, 1), (36, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (46, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (36, 1), (50, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (36, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (46, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (46, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (56, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB7
