import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6ef2b7fbffc72ea0c9400ecfd7f0af675431cc10798685f2eaba88869c9f5261"
def certificateSHA256 : String := "4ab3fdb85da648589dbcc40057d4e47b71614eb6158f0919bf36f79658578860"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 662 := ![
  7,
  13,
  17,
  22,
  25,
  149,
  150,
  168,
  179,
  198,
  211,
  212,
  237,
  298,
  301,
  302,
  308,
  314,
  315,
  316,
  359,
  383,
  422,
  432,
  434,
  436,
  443,
  444,
  460,
  463,
  505,
  548,
  556,
  578,
  601,
  608,
  645,
  653,
  655,
  656,
  657,
  658,
  659,
  660,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (32, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (22, 1), (32, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (22, 1), (32, 1), (42, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (32, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (32, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (36, 1), (42, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (20, 1), (32, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (42, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (32, 1), (36, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (32, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (32, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (32, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (18, 1), (21, 1), (32, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (29, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (45, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (45, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (42, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (15, 1), (20, 1), (27, 1), (32, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (25, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (20, 1), (27, 1), (32, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (26, 1), (32, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (32, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (32, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (32, 1), (36, 1), (42, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (18, 1), (21, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (18, 1), (21, 1), (32, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (18, 1), (21, 1), (25, 1), (32, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (21, 1), (25, 1), (32, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB2_0.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB2_0
