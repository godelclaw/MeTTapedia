import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "117aa0b181629ecb71b6d80321e9090f8772926d95e2ae91bd214253b7db8d9f"
def certificateSHA256 : String := "271094202d9020795c69be0b566c04346606b93d98e4c2adbfeceaa1fc426020"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 608 := ![
  1,
  2,
  3,
  4,
  6,
  7,
  8,
  41,
  150,
  202,
  210,
  308,
  309,
  311,
  324,
  325,
  364,
  378,
  438,
  462,
  465,
  541,
  558,
  569,
  570,
  593,
  600,
  601,
  602,
  603,
  604,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (36, 1), (50, 2), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (31, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (34, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (50, 2), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (23, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (54, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (13, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (21, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (32, 1), (36, 1), (50, 2), (55, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (17, 1), (32, 1), (36, 1), (50, 2), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (50, 2), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(1, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (23, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (23, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (21, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (37, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (37, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (44, 1), (50, 2), (55, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (44, 1), (50, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (23, 1), (37, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (23, 1), (37, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (23, 1), (44, 1), (50, 2), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (23, 1), (44, 1), (50, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (17, 1), (32, 1), (36, 1), (46, 1), (50, 3), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (32, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (32, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (21, 1), (23, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (21, 1), (23, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (44, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (32, 1), (50, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (32, 1), (54, 2), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (13, 1), (23, 1), (50, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (13, 1), (23, 1), (54, 2), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (31, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (15, 1), (26, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (13, 1), (21, 1), (23, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (26, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (23, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (23, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (21, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (50, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (54, 2), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (17, 1), (28, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (17, 1), (28, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (21, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (26, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (21, 1), (28, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (26, 1), (28, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB2_0.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB2_0
