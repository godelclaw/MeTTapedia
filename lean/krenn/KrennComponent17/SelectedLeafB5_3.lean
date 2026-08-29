import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c99ca62b19fcbfefc8198a23de6e8af50095337c53363213fd3e1e5dde058ec7"
def certificateSHA256 : String := "3efddcab0728f360a535194f9bb9ebddd5e9e3d1eeb187b3ef7770a87205cdc0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 608 := ![
  12,
  13,
  20,
  26,
  27,
  33,
  39,
  206,
  310,
  312,
  328,
  410,
  427,
  445,
  549,
  553,
  557,
  568,
  599,
  604,
  605,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 63) := ![
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (27, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (22, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (3, 1), (44, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (6, 1), (48, 1), (57, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (44, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (36, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (19, 1), (48, 1), (57, 2), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (30, 1), (36, 1), (57, 2), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (36, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (27, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (36, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (27, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (36, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(27, 1), (30, 1), (36, 2), (57, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (22, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (36, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (22, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (36, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (30, 1), (36, 2), (57, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (14, 1), (40, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (14, 1), (44, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (27, 1), (50, 2), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (27, 1), (50, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (27, 1), (54, 2), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (19, 1), (40, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (19, 1), (44, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (30, 1), (36, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (30, 1), (36, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (36, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (36, 1), (42, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [(44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (50, 2), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (27, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (54, 2), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (36, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 2), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (40, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (40, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (36, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (36, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (14, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (19, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 2), (42, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (6, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 2), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (3, 1), (14, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 2), (3, 1), (40, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (6, 1), (14, 1), (48, 1), (57, 2)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (6, 1), (33, 1), (40, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (14, 1), (19, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (14, 1), (24, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (14, 1), (30, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (40, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (36, 1), (40, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (36, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (24, 1), (27, 1), (50, 2), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (24, 1), (27, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (24, 1), (27, 1), (54, 2), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (14, 1), (19, 1), (48, 1), (57, 2)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (14, 1), (30, 1), (36, 1), (57, 2)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (19, 1), (33, 1), (40, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (24, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (30, 1), (33, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (33, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (24, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (19, 1), (24, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (24, 1), (30, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_3
