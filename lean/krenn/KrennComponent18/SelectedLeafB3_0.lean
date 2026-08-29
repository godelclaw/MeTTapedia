import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1402df9c94e556dcc0d7e623efeff4f6b08e1a433288b17f2ac31f626557b778"
def certificateSHA256 : String := "a2aa100d44b3729aab7b4c9f7fa6b4b4152f89777d471a09eb875f6e451e3918"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 664 := ![
  1,
  7,
  8,
  9,
  10,
  11,
  19,
  147,
  162,
  170,
  301,
  302,
  318,
  393,
  408,
  430,
  437,
  443,
  449,
  450,
  478,
  479,
  494,
  516,
  580,
  581,
  585,
  602,
  603,
  655,
  657,
  658,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (38, 1), (59, 2)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (37, 1), (40, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (46, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 2), (32, 1), (37, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (32, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (32, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (19, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (37, 1), (40, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (31, 1), (38, 1), (46, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (37, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (37, 1), (40, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (62, 1)] }, { coefficient := 2, powers := [(25, 1), (30, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 2), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (25, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(17, 1), (25, 1), (30, 1), (62, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (30, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 2), (13, 1), (32, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (19, 1), (37, 1), (40, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (37, 1), (40, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (14, 1), (37, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (37, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (37, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (38, 1), (46, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (14, 1), (37, 1), (40, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (37, 1), (38, 1), (40, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (24, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (30, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (25, 1), (30, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (38, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := -1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (37, 1), (40, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (13, 1), (35, 1), (37, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 2), (13, 1), (32, 1), (37, 1), (40, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (13, 1), (19, 1), (37, 1), (40, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 3), (13, 1), (32, 1), (35, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (13, 1), (14, 1), (25, 1), (32, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 2), (13, 1), (19, 1), (35, 1), (37, 1), (40, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (14, 1), (19, 1), (25, 1), (37, 1), (40, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 2), (30, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (23, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (25, 1), (30, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (25, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (31, 1), (38, 1), (46, 1), (59, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB3_0.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB3_0
