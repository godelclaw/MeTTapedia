import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "eac39a9c63cd44a4c60903191c026a9658fe52b928b8ad9c8ac8940af4a5f9c3"
def certificateSHA256 : String := "53199f06ed6c81825997bec68a5c761bce27ca5442d51e450a03742ab516203f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 670 := ![
  5,
  171,
  280,
  294,
  295,
  298,
  299,
  310,
  312,
  313,
  317,
  394,
  410,
  411,
  424,
  446,
  450,
  466,
  475,
  482,
  505,
  510,
  519,
  561,
  604,
  646,
  649,
  656,
  657,
  658,
  659,
  662,
  664,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(4, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (42, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (42, 1), (52, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (55, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (42, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (39, 1), (51, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (42, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (52, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (36, 1), (55, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (30, 1), (36, 1), (55, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (42, 1), (44, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (49, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (47, 1), (52, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (22, 1), (36, 1), (41, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (22, 1), (36, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (22, 1), (36, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (41, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (46, 2), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (32, 1), (36, 1), (38, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (41, 2), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (41, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (41, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (36, 1), (38, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (39, 1), (41, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1), (47, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (42, 1), (47, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (41, 1), (51, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (45, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (46, 1), (51, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1), (42, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (41, 1), (42, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (22, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (52, 1), (55, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_6_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_6_1
