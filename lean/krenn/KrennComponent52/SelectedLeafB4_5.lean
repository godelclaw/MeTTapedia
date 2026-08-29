import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component52.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d4aa8b8f724aae6fc289eb9103fef342ef5d9f1862cc4fd6be49e87f193b5cd2"
def certificateSHA256 : String := "89601db5832dabc9db9f1af38db5c4d5de3d726cd8d1104ba2ecbd4576a5e9fb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 640 := ![
  6,
  9,
  23,
  30,
  161,
  162,
  221,
  233,
  310,
  313,
  346,
  353,
  354,
  379,
  467,
  633,
  634,
  636,
  637,
  638,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (41, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (41, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (41, 1), (45, 1), (60, 1), (62, 2)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (41, 1), (45, 1), (52, 1), (62, 2)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (41, 1), (47, 1), (60, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (41, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (41, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (41, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (41, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (41, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (41, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (41, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (41, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(41, 2), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (41, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (41, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (41, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (32, 1), (41, 1), (47, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }]
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

#print axioms Krenn.Component52.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component52.SelectedLeafB4_5
