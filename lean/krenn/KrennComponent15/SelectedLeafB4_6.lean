import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cc0ee55240d0f4950edc28d3ed772a4546793a07186bc7d6878896df78bae720"
def certificateSHA256 : String := "f7e8d68ff4df98c585830db9e326fdef7e2d8627034335fb29456a74ae879976"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 592 := ![
  12,
  13,
  21,
  25,
  29,
  178,
  209,
  226,
  227,
  234,
  315,
  359,
  360,
  362,
  363,
  364,
  365,
  366,
  367,
  368,
  379,
  423,
  467,
  471,
  481,
  496,
  506,
  519,
  546,
  584,
  585,
  586,
  587,
  588,
  590,
  591
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(28, 1), (33, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(3, 1), (11, 1), (29, 1), (42, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (29, 1), (37, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (33, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (33, 1), (42, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (34, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (11, 1), (19, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (29, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(26, 1), (44, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(21, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (21, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (26, 1), (57, 1)] }, { coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (29, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (29, 1), (42, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (29, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (29, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(5, 1), (26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (37, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (42, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := -1, powers := [(40, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (25, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB4_6.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB4_6
