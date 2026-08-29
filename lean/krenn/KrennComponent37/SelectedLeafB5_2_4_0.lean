import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_4_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "57da2ca91686bd5cf16aea2c111ac40f1d3007c38cb52c7873bdf64010ab502d"
def certificateSHA256 : String := "1bc61e9599dc9fc49d3b4e4dc0d26532695ebffc4fea0cf6c1957a521a22494b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 670 := ![
  6,
  13,
  17,
  171,
  179,
  181,
  300,
  349,
  410,
  411,
  437,
  438,
  444,
  449,
  450,
  453,
  454,
  487,
  515,
  561,
  566,
  583,
  603,
  619,
  655,
  657,
  660,
  661,
  663,
  664,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (36, 1), (37, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (36, 1), (37, 1), (43, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (23, 1), (36, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (23, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (20, 1), (36, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (37, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1), (37, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (37, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (36, 1), (37, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1), (43, 1), (50, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (26, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (37, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (43, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (36, 1), (37, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (36, 1), (37, 1), (43, 1), (50, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (43, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (36, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (43, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (36, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (36, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (18, 1), (20, 1), (28, 1), (36, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (20, 1), (28, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (31, 1), (36, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (37, 1), (43, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (31, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (34, 1), (36, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 2), (36, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (34, 1), (36, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (26, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (36, 1), (37, 1), (55, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (36, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (43, 1), (55, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (40, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (21, 1), (36, 1), (37, 1), (41, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (36, 1), (37, 1), (41, 1), (43, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (26, 1), (37, 1), (41, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (26, 1), (37, 1), (46, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (37, 1), (41, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (37, 1), (46, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (39, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (39, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (41, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (37, 1), (48, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_4_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_4_0
