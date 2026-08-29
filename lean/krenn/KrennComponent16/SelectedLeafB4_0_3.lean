import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB4_0_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "80249b19a66f39c3145db0e488c62b73da99bcdd33072a10e664737482783094"
def certificateSHA256 : String := "e7ac0d0a6493a05f0274a70928e824660903212d0b39b7e86acb82f804afa631"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 671 := ![
  9,
  10,
  12,
  13,
  21,
  23,
  31,
  142,
  150,
  162,
  166,
  167,
  170,
  175,
  176,
  247,
  273,
  299,
  300,
  301,
  302,
  314,
  315,
  316,
  317,
  321,
  325,
  394,
  408,
  436,
  440,
  448,
  571,
  573,
  593,
  595,
  608,
  609,
  660,
  661,
  663,
  664,
  666,
  667,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(11, 1), (23, 1), (25, 1), (47, 1), (53, 2), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (50, 1), (53, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1), (50, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (25, 1), (53, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := -4, powers := [(11, 1), (25, 1), (47, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(11, 1), (25, 1), (53, 1), (57, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(16, 1), (25, 1), (53, 2), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(31, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (13, 1), (25, 1), (45, 1), (53, 1), (58, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (25, 1), (45, 1), (47, 1), (53, 1), (58, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (25, 1), (47, 1), (53, 1), (58, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (45, 1), (47, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (23, 1), (25, 1), (47, 1), (53, 2), (58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (25, 1), (33, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(16, 1), (21, 1), (23, 1), (25, 1), (53, 2), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(31, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (47, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (23, 1), (25, 1), (53, 2), (58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (13, 1), (25, 1), (53, 1), (58, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (25, 1), (47, 1), (53, 1), (58, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (53, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (47, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (25, 1), (53, 2), (58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (25, 1), (47, 1), (53, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (47, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (30, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (47, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (25, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(16, 1), (25, 1), (53, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (47, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (25, 1), (47, 1), (53, 1), (58, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (25, 1), (28, 1), (53, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (16, 1), (25, 1), (53, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (25, 1), (53, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (25, 1), (39, 1), (53, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (47, 1), (48, 1), (53, 1), (54, 1), (58, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (47, 1), (53, 2), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(50, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (13, 1), (25, 1), (47, 1), (53, 1), (58, 2), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(1, 1), (13, 1), (25, 1), (53, 1), (57, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (25, 1), (36, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (25, 1), (28, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (45, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (25, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(4, 1), (13, 1), (25, 1), (33, 1), (47, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (23, 1), (25, 1), (53, 1), (58, 1), (60, 1), (63, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB4_0_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB4_0_3
