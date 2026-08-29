import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_1_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3cd31df1e124fb768f70cb1389160a08b686efe996b8b5e81522f77d1fc4c34c"
def certificateSHA256 : String := "2e97e9cdc22e28de5bd9b9bc71999857af1e2ee5739aa900945189b105509983"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 670 := ![
  183,
  184,
  185,
  296,
  297,
  298,
  299,
  312,
  315,
  316,
  364,
  366,
  454,
  471,
  472,
  478,
  480,
  485,
  505,
  510,
  526,
  529,
  567,
  580,
  604,
  656,
  659,
  662,
  663,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(26, 1), (48, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (48, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (46, 1), (48, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (48, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1), (46, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (22, 1), (33, 1), (39, 1), (63, 1), (66, 2)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (48, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(30, 1), (48, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(55, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (48, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (29, 1), (46, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (46, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(29, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (38, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (33, 1), (39, 1), (46, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (39, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (39, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (33, 1), (39, 1), (63, 1), (66, 2)] }],
  [{ coefficient := 1, powers := [(21, 1), (55, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (30, 1), (33, 1), (39, 1), (63, 1), (66, 2)] }],
  [{ coefficient := 1, powers := [(33, 1), (39, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1), (48, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (46, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (46, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (33, 1), (39, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (35, 1), (39, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (30, 1), (33, 1), (39, 1), (63, 1), (66, 2)] }, { coefficient := -1, powers := [(21, 1), (28, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (51, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (33, 1), (39, 1), (46, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (33, 1), (39, 1), (52, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (33, 1), (39, 1), (57, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (33, 1), (39, 1), (46, 2), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (33, 1), (39, 1), (46, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (33, 1), (39, 1), (46, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (33, 1), (39, 1), (41, 1), (46, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (33, 1), (39, 1), (41, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (33, 1), (39, 1), (41, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (41, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (46, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (41, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (46, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (51, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (46, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (42, 1), (46, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (39, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (41, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (33, 1), (39, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (33, 1), (39, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (33, 1), (39, 1), (46, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (33, 1), (39, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_1_6_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_1_6_1
