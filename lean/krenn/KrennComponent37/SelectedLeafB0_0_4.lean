import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_0_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "067e242e2a95585088e084990377021f9daec450b0645ad2adb6a56163026851"
def certificateSHA256 : String := "f6ed4ca45ebac05dd5b41d5c40ec411cd8e18af419b6a77163dfb48118b78159"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 667 := ![
  171,
  175,
  179,
  256,
  280,
  285,
  295,
  307,
  312,
  314,
  315,
  316,
  317,
  393,
  396,
  411,
  415,
  424,
  430,
  432,
  438,
  445,
  446,
  450,
  453,
  460,
  467,
  471,
  475,
  482,
  483,
  555,
  566,
  570,
  608,
  623,
  647,
  657,
  658,
  660,
  662,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(30, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (44, 1), (48, 1)] }, { coefficient := 2, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := -2, powers := [(25, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (44, 1), (48, 1)] }, { coefficient := -2, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (48, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (28, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (36, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (36, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (46, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (30, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (44, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (39, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (46, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := 1, powers := [(44, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (30, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (30, 1), (34, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (25, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (33, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }]
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
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_0_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_0_4
