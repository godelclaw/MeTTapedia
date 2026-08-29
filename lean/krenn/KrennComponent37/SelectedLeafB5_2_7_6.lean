import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0245b9db1b5ee3b625ff935d362b80fb78222093ea721822f123ca40b0d9ff07"
def certificateSHA256 : String := "c53618518e279fa917f6bcfa30e45719c061cd5aabd18112514bdcb288a981a9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 670 := ![
  13,
  15,
  17,
  25,
  28,
  148,
  149,
  150,
  179,
  180,
  181,
  222,
  300,
  301,
  358,
  433,
  438,
  487,
  566,
  583,
  591,
  602,
  603,
  655,
  657,
  660,
  661,
  663,
  665,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (37, 1), (59, 1), (63, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (37, 1), (59, 1), (63, 1), (69, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (59, 1), (63, 1), (69, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (28, 1), (59, 1), (63, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (31, 1), (37, 1), (44, 1), (55, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1), (69, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (50, 1), (69, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (31, 1), (37, 1), (55, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (37, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (56, 1), (57, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (69, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (18, 1), (31, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (18, 1), (31, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (13, 1), (31, 1), (37, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (13, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (26, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (33, 1), (37, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (56, 1), (57, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (43, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (31, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (31, 1), (36, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (31, 1), (37, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (23, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (31, 1), (37, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (31, 1), (37, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (31, 1), (37, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (31, 1), (37, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (31, 1), (37, 1), (42, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_7_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_7_6
