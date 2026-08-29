import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB2_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3a30abfa9616cfca264f5e96d94c11cdd7d5258e84c79753e292cc1ef706c389"
def certificateSHA256 : String := "8361ce6d801f466e55f559222c9c8d5452e1e008f0bed8b5c0e47096d423d1a2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 665 := ![
  7,
  10,
  13,
  14,
  22,
  25,
  149,
  150,
  152,
  178,
  206,
  211,
  212,
  292,
  297,
  298,
  301,
  302,
  303,
  312,
  359,
  443,
  454,
  463,
  556,
  583,
  600,
  601,
  608,
  653,
  655,
  656,
  657,
  658,
  659,
  661,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (35, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (25, 1), (27, 1), (48, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (25, 1), (53, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (36, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (25, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (25, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (36, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (42, 1), (48, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (36, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (36, 1), (42, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (16, 1), (22, 1), (25, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (29, 1), (36, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (36, 1), (42, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (53, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (25, 1), (29, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (26, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (36, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (36, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (42, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (19, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (26, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (26, 1), (46, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (40, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (46, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(36, 1), (58, 1)] }, { coefficient := -1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (25, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (25, 1), (26, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (29, 1), (36, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (29, 1), (36, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (27, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (29, 1), (36, 1), (42, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (29, 1), (36, 1), (42, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (42, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (36, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (25, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (25, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (29, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (30, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB2_2_7.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB2_2_7
