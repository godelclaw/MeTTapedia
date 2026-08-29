import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_2_3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "43620ce28bce58cec48abd75b11167d55e157477e38bc02c1c60fb4f0231053b"
def certificateSHA256 : String := "ac52ae883e90cd64c0d60f65eae019d78ca8233baa744e8d8fb428843f979215"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 614 := ![
  5,
  7,
  8,
  14,
  18,
  37,
  38,
  41,
  308,
  309,
  311,
  325,
  326,
  364,
  378,
  430,
  441,
  480,
  494,
  569,
  570,
  600,
  601,
  603,
  607,
  609,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (38, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (38, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (38, 1), (50, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (26, 1), (31, 1), (54, 1), (55, 1), (65, 2)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (26, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 2), (44, 1), (55, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (40, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (44, 1), (50, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (44, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (44, 1), (55, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (27, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (26, 1), (34, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (26, 2), (55, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (26, 1), (31, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (26, 1), (34, 1), (50, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (26, 1), (34, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (55, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (54, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (26, 1), (32, 1), (54, 1), (55, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 2), (55, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (50, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (55, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (29, 1), (32, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (26, 1), (32, 1), (50, 1), (54, 1), (55, 1), (65, 2)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (37, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (40, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (44, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (44, 1), (54, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (26, 2), (32, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (26, 1), (32, 1), (34, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (26, 1), (32, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (21, 1), (26, 1), (32, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (26, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (26, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (26, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (50, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_2_3_7.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_2_3_7
