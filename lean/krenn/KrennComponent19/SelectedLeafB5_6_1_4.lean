import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_6_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8b38ff10f72eddf0e7d9a45995327f2f445360fb08ee184e06bb733f3133a6be"
def certificateSHA256 : String := "5b99be2e810231b7734656c4ef6c62cccca4afd136b43c4a7cea484a78e45e24"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 675 := ![
  0,
  4,
  7,
  10,
  18,
  19,
  20,
  22,
  29,
  31,
  171,
  196,
  316,
  318,
  331,
  403,
  420,
  424,
  429,
  442,
  502,
  565,
  583,
  607,
  661,
  662,
  663,
  664,
  665,
  668,
  670,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(32, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 68) := ![
  [{ coefficient := -2, powers := [(2, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (58, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (27, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (30, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (38, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (20, 1), (26, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (25, 1), (26, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (38, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (25, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (21, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (21, 1), (41, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (48, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (21, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 2), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (38, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (27, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (27, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (27, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (35, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (25, 1), (26, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (21, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (23, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (25, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (35, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (35, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (37, 1), (53, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_6_1_4.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_6_1_4
