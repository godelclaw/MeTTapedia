import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_5_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "14effe4fb2a8685a5ea7bbf2a4265bd7fc035e1a1f93ead55e2883f335950499"
def certificateSHA256 : String := "a12de869c89ea40302609d36135a807866d61d4be05bb3f26a4132f684ff0dd8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 670 := ![
  16,
  19,
  79,
  148,
  151,
  171,
  180,
  185,
  295,
  298,
  299,
  303,
  312,
  317,
  433,
  446,
  450,
  485,
  505,
  510,
  604,
  656,
  657,
  659,
  660,
  661,
  662,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (38, 1), (42, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (63, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (36, 1), (39, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (30, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(12, 1), (36, 1), (38, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (35, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (30, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (36, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (22, 1), (36, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (22, 1), (36, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (22, 1), (36, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (22, 1), (36, 1), (39, 1), (46, 2)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (22, 1), (36, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (22, 1), (36, 1), (39, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (36, 1), (39, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (36, 1), (39, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (36, 1), (39, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (36, 1), (39, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (36, 1), (42, 1), (46, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (36, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (40, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (22, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (36, 1), (39, 1), (52, 1)] }]
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

#print axioms Krenn.Component37.SelectedLeafB4_5_2_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_5_2_1
