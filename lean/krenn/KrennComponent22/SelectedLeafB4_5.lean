import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "20d237373bc97717f15d17cdbfec5941d11cd485c13b5a1204a5dd0076516cca"
def certificateSHA256 : String := "a3ba1c71b4be32e364d0fae65040368869ecbefc903977d1d6de9a2b466dfd4e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 642 := ![
  2,
  3,
  20,
  168,
  184,
  201,
  205,
  208,
  218,
  237,
  278,
  311,
  351,
  353,
  359,
  363,
  364,
  467,
  557,
  629,
  635,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (29, 1), (32, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 2), (56, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (35, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (22, 1), (32, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 2), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (41, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (32, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (16, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (38, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (41, 1), (56, 2), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (47, 1), (53, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (43, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (24, 1), (32, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (24, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (24, 1), (32, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (24, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB4_5
