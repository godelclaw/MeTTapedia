import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_1_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "550a21377dda88f90cb0fad686574814ed186a0d4455e4b1d1407258b3901951"
def certificateSHA256 : String := "0b316251107d8872f8be478ca644875bf3c304feae4ec1c7a55dfbc6a4099341"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 614 := ![
  25,
  30,
  36,
  194,
  300,
  306,
  308,
  326,
  358,
  427,
  432,
  445,
  446,
  454,
  465,
  468,
  484,
  494,
  509,
  550,
  569,
  600,
  602,
  603,
  604,
  606,
  609,
  610,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (22, 1), (34, 1), (50, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (28, 1), (34, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (34, 1), (50, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (27, 1), (50, 1), (57, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (28, 1), (57, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (31, 1), (50, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (34, 1), (50, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (31, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(7, 1), (28, 1), (34, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (34, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (34, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (31, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (31, 1), (37, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (51, 1), (57, 1), (59, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (26, 1), (57, 1), (59, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (51, 1), (57, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (34, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (34, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (50, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (27, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (34, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (34, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (51, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (57, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (51, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (44, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (26, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (34, 1), (40, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (34, 1), (44, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (40, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (44, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(15, 1), (26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (37, 1), (57, 2)] }, { coefficient := 2, powers := [(37, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (34, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (36, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (36, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (17, 1), (22, 1), (34, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (29, 1), (34, 1), (40, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (29, 1), (34, 1), (44, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (28, 1), (34, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (34, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (27, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (27, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (27, 1), (34, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (34, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (29, 1), (40, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (29, 1), (44, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (28, 1), (51, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (22, 1), (34, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (28, 1), (34, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (22, 1), (34, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (26, 1), (27, 1), (50, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (28, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (27, 1), (31, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (27, 1), (34, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (28, 1), (31, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (28, 1), (34, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (26, 1), (43, 1), (51, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (26, 1), (43, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (22, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (27, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (22, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (27, 1), (31, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_1_7.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_1_7
