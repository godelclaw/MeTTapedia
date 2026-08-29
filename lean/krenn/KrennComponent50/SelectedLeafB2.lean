import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component50.SelectedLeafB2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9abbd452910d366061dce37a7e456a84d479111ed7a06f4e1b96b80f652bce2b"
def certificateSHA256 : String := "1829137ec042bca2b0eab449e05ebb6a0de80ec209f0690c11f3559aaa8e0eef"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 638 := ![
  2,
  3,
  206,
  207,
  209,
  211,
  228,
  243,
  362,
  363,
  477,
  478,
  634,
  635,
  637
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (36, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(42, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component50.SelectedLeafB2.selectedHasNoCommonZero

end Krenn.Component50.SelectedLeafB2
