import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB4_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a9b9622bffff015bce123f0d06707d77bd74088e38ac25fdc81784d7612bb651"
def certificateSHA256 : String := "3b45b560a56812809cedb79b9ee82ba8537f44771221afbe1b8e360c4187b727"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 642 := ![
  2,
  3,
  21,
  205,
  208,
  237,
  311,
  351,
  353,
  363,
  364,
  460,
  467,
  557,
  635,
  638,
  640,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (29, 1), (32, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 2), (56, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (35, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (29, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (22, 1), (32, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 2), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (32, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (16, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (38, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (47, 1), (53, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (24, 1), (32, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (24, 1), (32, 1), (46, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (24, 1), (32, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (24, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (6, 1), (32, 1), (56, 2), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (8, 1), (32, 1), (35, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB4_4.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB4_4
