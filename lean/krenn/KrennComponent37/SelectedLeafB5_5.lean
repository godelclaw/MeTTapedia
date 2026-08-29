import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1255e12900d05ac7e578df1e7c1a7943c097eebbe86a580186e4d497e0462813"
def certificateSHA256 : String := "c0f78cfdc64c2f9414551120ab833b462459f19fb05c2f4992c787cd2bd90358"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 664 := ![
  8,
  16,
  19,
  71,
  149,
  151,
  152,
  153,
  171,
  179,
  180,
  181,
  196,
  221,
  295,
  303,
  315,
  317,
  335,
  425,
  432,
  433,
  438,
  445,
  446,
  449,
  450,
  453,
  478,
  487,
  580,
  583,
  584,
  619,
  657,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (29, 1), (33, 1), (44, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (28, 1), (36, 1), (37, 1), (46, 1), (54, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (36, 1), (37, 1), (46, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (36, 1), (39, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (36, 1), (37, 1), (46, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (36, 1), (37, 1), (54, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (36, 1), (39, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (36, 1), (37, 1), (48, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (28, 1), (37, 1), (46, 1), (54, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (46, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (46, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(24, 1), (37, 1), (54, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 1), (48, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(30, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (44, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (46, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (33, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (49, 1), (52, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (51, 1), (52, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (36, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (28, 1), (36, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (52, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (49, 1), (51, 1), (52, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (40, 1), (44, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (21, 1), (28, 1), (36, 1), (37, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (21, 1), (30, 1), (36, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (24, 1), (26, 1), (36, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (24, 1), (36, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (36, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (30, 1), (36, 1), (37, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (28, 1), (37, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (25, 1), (49, 1), (51, 1), (52, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (21, 1), (28, 1), (36, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (21, 1), (30, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (24, 1), (26, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (28, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (49, 1), (52, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_5
