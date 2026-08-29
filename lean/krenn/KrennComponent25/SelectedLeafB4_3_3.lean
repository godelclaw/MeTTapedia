import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB4_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "97909f663b2cedfd0591059d69e7c14c60f536dc8c101d979968fa32975e153e"
def certificateSHA256 : String := "73e4eee5c3bf6f2731577746452016ed69171625701d679ac0508b671186eebc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 665 := ![
  3,
  8,
  11,
  14,
  15,
  16,
  17,
  19,
  21,
  142,
  162,
  170,
  173,
  175,
  188,
  257,
  300,
  311,
  312,
  327,
  352,
  388,
  430,
  435,
  439,
  450,
  588,
  602,
  603,
  604,
  605,
  648,
  654,
  655,
  657,
  658,
  660,
  661,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(3, 1), (17, 1), (34, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (20, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (25, 1), (41, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (26, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (20, 1), (29, 1), (41, 1), (45, 1), (56, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (21, 1), (29, 1), (41, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (21, 1), (29, 1), (41, 1), (56, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (25, 1), (29, 1), (41, 1), (52, 1), (56, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (26, 1), (29, 1), (40, 1), (41, 1), (65, 1)] }, { coefficient := 4, powers := [(17, 1), (26, 1), (29, 1), (41, 1), (45, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (26, 1), (29, 1), (41, 1), (56, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (31, 1), (37, 1), (41, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (17, 1), (19, 1), (29, 1), (34, 1), (41, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (53, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(24, 1), (29, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (41, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (41, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (52, 1), (56, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1), (56, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (40, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (29, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (17, 1), (29, 1), (41, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (52, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (17, 1), (34, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (17, 1), (34, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (17, 1), (29, 1), (34, 1), (41, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (29, 1), (31, 1), (37, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (29, 1), (41, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (17, 1), (34, 1), (41, 1), (45, 1)] }, { coefficient := -2, powers := [(17, 1), (20, 1), (41, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (25, 1), (41, 1), (52, 1)] }, { coefficient := -2, powers := [(17, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1)] }, { coefficient := -2, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (29, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (29, 1), (41, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (17, 1), (29, 1), (34, 1), (41, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (20, 1), (29, 1), (41, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(10, 1), (17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(17, 1), (29, 1), (37, 1), (41, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (40, 1), (41, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (29, 1), (40, 1), (41, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (41, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(41, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (14, 1), (17, 1), (29, 1), (34, 1), (41, 1), (45, 1), (52, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (29, 1), (31, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (17, 1), (23, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (17, 1), (29, 1), (31, 1), (41, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (21, 1), (29, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (17, 1), (20, 1), (29, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := -2, powers := [(10, 1), (17, 1), (21, 1), (29, 1), (41, 1), (52, 1)] }, { coefficient := 2, powers := [(10, 1), (17, 1), (25, 1), (29, 1), (41, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(10, 1), (17, 1), (26, 1), (29, 1), (40, 1), (41, 1)] }, { coefficient := -4, powers := [(10, 1), (17, 1), (26, 1), (29, 1), (41, 1), (45, 1)] }, { coefficient := -2, powers := [(10, 1), (17, 1), (26, 1), (29, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(10, 1), (17, 1), (29, 1), (31, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (52, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (23, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (29, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (24, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1), (46, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (23, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (29, 1), (53, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB4_3_3.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB4_3_3
