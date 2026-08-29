import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_3_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dfad86f5e592ccfd4cf78d1114990aceaba565aaaf311e72d37e7693f6e9f410"
def certificateSHA256 : String := "2a4664b09ee1edfe3c6a277f023474426eab2467d2646f93a4a3abe7144808c3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 675 := ![
  24,
  139,
  233,
  276,
  302,
  303,
  313,
  319,
  407,
  504,
  549,
  552,
  594,
  607,
  608,
  623,
  661,
  664,
  668,
  670,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(16, 1), (40, 1), (43, 1), (58, 1), (65, 2)] }, { coefficient := 1, powers := [(16, 1), (43, 1), (45, 1), (58, 1), (65, 2)] }, { coefficient := 2, powers := [(16, 1), (43, 1), (52, 1), (58, 1), (65, 2)] }],
  [{ coefficient := -1, powers := [(34, 1), (37, 1), (47, 1), (53, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (53, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (40, 1), (58, 1), (65, 2)] }, { coefficient := -1, powers := [(16, 1), (45, 1), (58, 1), (65, 2)] }, { coefficient := -2, powers := [(16, 1), (52, 1), (58, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(45, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(46, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (21, 1), (58, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (47, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (58, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (37, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1), (58, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (57, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(40, 1), (47, 1), (53, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(45, 1), (52, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (40, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (29, 1), (58, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (34, 1), (37, 1), (47, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (34, 1), (37, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (25, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (21, 1), (40, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (45, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(16, 1), (21, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (40, 1), (47, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (40, 1), (41, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (45, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (40, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (45, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (52, 1), (58, 1), (65, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_3_1_5.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_3_1_5
