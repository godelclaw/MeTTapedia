import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7afb66e54da2fd475f48b8fb6b54351177abfafdb35a1a35d0c2d5e3cf33acd1"
def certificateSHA256 : String := "8df97ca962104365c7c75984800b71f671f09a762cca4356d694b56c71cddf31"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 592 := ![
  10,
  16,
  17,
  19,
  20,
  26,
  45,
  101,
  110,
  232,
  234,
  336,
  363,
  364,
  365,
  366,
  367,
  368,
  376,
  443,
  475,
  506,
  527,
  546,
  584,
  585,
  587,
  588,
  589,
  590,
  591
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (32, 1), (38, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (19, 1), (32, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (26, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (21, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (32, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (32, 1), (34, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (32, 1), (35, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (31, 1), (32, 1), (34, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (12, 1), (31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (35, 1), (55, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (38, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (38, 1), (52, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (29, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (32, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (32, 1), (35, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (32, 1), (38, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (11, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(12, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (34, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := 1, powers := [(38, 1), (53, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (31, 1), (32, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (31, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (19, 1), (32, 1), (35, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (40, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (32, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (29, 1), (40, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (29, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (31, 1), (32, 1), (38, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (31, 1), (32, 1), (35, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (24, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (22, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (31, 1), (32, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (31, 1), (32, 1), (34, 1), (35, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB4_5
