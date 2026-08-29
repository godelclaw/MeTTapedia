import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4347804d2662b27723b2f8c710599660fc39b1dd970292a085a393e1ef01c1dc"
def certificateSHA256 : String := "05df5ba8e0eee3d1f2ddd46744257343a5156b8ca3bdd0fae91578850e8cecb2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 667 := ![
  1,
  2,
  4,
  6,
  7,
  8,
  9,
  184,
  193,
  430,
  434,
  440,
  566,
  607,
  645,
  660,
  661,
  662,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (47, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (47, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (49, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB7_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB7_0
