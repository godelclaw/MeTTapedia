import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4f78dcf8e57297316c541370077ce360843f558a1d7116f66fd7816982268ce6"
def certificateSHA256 : String := "2cd18ca12b4a72ff8d4694e3b7460afd341ec35ef5c98f6024275bd280fd6be6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 589 := ![
  1,
  2,
  4,
  5,
  7,
  9,
  10,
  13,
  14,
  17,
  44,
  45,
  226,
  227,
  363,
  364,
  365,
  366,
  384,
  398,
  413,
  420,
  421,
  429,
  471,
  519,
  545,
  546,
  584,
  585,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (8, 1), (32, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (32, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (24, 1), (29, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (19, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (32, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (29, 1), (37, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (29, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (31, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (19, 1), (29, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (19, 1), (29, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (24, 1), (29, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (38, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (21, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (28, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (15, 1), (31, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (29, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (32, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (29, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (29, 1), (37, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (29, 1), (37, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (29, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (29, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (32, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (32, 1), (37, 1), (38, 1), (42, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (32, 1), (37, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (32, 1), (38, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (32, 1), (38, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (31, 1), (32, 1), (38, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (19, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (24, 1), (29, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (19, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (24, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (19, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (32, 1), (38, 1), (42, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB7
