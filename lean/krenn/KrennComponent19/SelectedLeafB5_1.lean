import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ae9d4f17a085cabd225a25e072cf93f4cad3297fb978813b8ada25b2a07f08bd"
def certificateSHA256 : String := "dd01afff99f6a11164b1b407135224d0bb8c0f070d351c53f81a3c3518179921"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 669 := ![
  2,
  10,
  17,
  18,
  20,
  22,
  23,
  24,
  170,
  191,
  203,
  304,
  318,
  403,
  412,
  420,
  424,
  428,
  429,
  463,
  468,
  565,
  610,
  662,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(32, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (38, 1), (44, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (38, 1), (44, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(21, 1), (25, 1), (49, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (39, 1), (54, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(30, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (39, 1), (44, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (53, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (32, 1), (50, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (39, 1), (48, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1), (39, 1), (44, 1), (48, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (32, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1)] }, { coefficient := -2, powers := [(13, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (38, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (38, 1), (39, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (35, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (35, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1), (46, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (27, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (38, 1), (39, 1), (44, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (32, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (27, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (35, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (24, 1), (38, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (30, 1), (38, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (27, 1), (49, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (25, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (32, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (27, 1), (39, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (39, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (38, 1), (39, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (39, 1), (44, 1), (54, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_1.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_1
