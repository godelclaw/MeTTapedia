import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "00d5e1fe770c6654839c6ef49dd27a66264614de4f96cfd93c56c0dabd339e0f"
def certificateSHA256 : String := "a7fc1a6d33d0122d70d01391eba9b2eb83d6b9ac8b158d14b6ae1cb96ddcb946"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 667 := ![
  0,
  1,
  3,
  4,
  5,
  23,
  171,
  175,
  257,
  283,
  294,
  296,
  298,
  310,
  312,
  411,
  450,
  484,
  485,
  562,
  566,
  567,
  570,
  649,
  650,
  657,
  658,
  659,
  660,
  662,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (58, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1), (58, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (36, 1), (37, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1), (44, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (42, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (61, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (44, 1), (61, 1), (63, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (51, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (42, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (61, 1), (63, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (61, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (42, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (58, 1), (66, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -2, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (42, 1), (44, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (51, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (47, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (30, 1), (61, 1), (63, 1), (64, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_3_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_3_3
