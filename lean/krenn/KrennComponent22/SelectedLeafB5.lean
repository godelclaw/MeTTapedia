import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cbd64d94c55671295a72e6532b617a18d71956edcb55efc9977b4b2b92ba06dc"
def certificateSHA256 : String := "e97fe20c364f7d12f04ac4f511117ffb3fe0e37cfcf210f813e82fe46d2bf555"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 639 := ![
  0,
  1,
  2,
  3,
  8,
  17,
  24,
  27,
  219,
  265,
  303,
  345,
  347,
  363,
  364,
  369,
  371,
  375,
  376,
  387,
  388,
  558,
  582,
  621,
  634,
  635,
  637,
  638
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (7, 1), (34, 1), (41, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (5, 1), (17, 1), (26, 1), (35, 1), (41, 1), (53, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (17, 1), (35, 1), (36, 1), (53, 1), (58, 1), (61, 2)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (17, 1), (34, 1), (41, 1), (55, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (26, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (26, 1), (41, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (41, 1), (45, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 2), (4, 1), (23, 1), (26, 1), (41, 1), (47, 1), (53, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 2), (23, 1), (36, 1), (47, 1), (53, 1), (58, 1), (61, 2)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (8, 1), (23, 1), (26, 1), (32, 1), (41, 1), (47, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (34, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (17, 1), (34, 1), (41, 1), (45, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (23, 1), (32, 1), (36, 1), (47, 1), (58, 1), (61, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (26, 1), (32, 1), (41, 1), (56, 2)] }, { coefficient := -1, powers := [(2, 1), (32, 1), (36, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (26, 1), (35, 1), (41, 2), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (36, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (34, 1), (37, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (4, 1), (41, 1), (56, 2), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (55, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (61, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (4, 1), (26, 1), (41, 1), (51, 1), (53, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 2), (36, 1), (51, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (8, 1), (26, 1), (32, 1), (41, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (32, 1), (36, 1), (51, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (5, 1), (26, 1), (35, 1), (41, 1), (45, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (35, 1), (36, 1), (45, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (16, 1), (26, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (36, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (12, 1), (26, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (36, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (5, 1), (26, 1), (35, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (35, 1), (36, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (4, 1), (26, 1), (41, 1), (53, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 2), (36, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (8, 1), (26, 1), (32, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (32, 1), (36, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (41, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (26, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (26, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 2), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (37, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (40, 1), (41, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 2), (4, 1), (23, 1), (26, 1), (41, 1), (47, 1), (51, 1), (53, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 2), (23, 1), (36, 1), (47, 1), (51, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (7, 1), (34, 1), (41, 1), (45, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (5, 1), (17, 1), (26, 1), (35, 1), (41, 1), (45, 1), (53, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (8, 1), (23, 1), (26, 1), (32, 1), (41, 1), (47, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (34, 1), (41, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (17, 1), (35, 1), (36, 1), (45, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (17, 1), (34, 1), (41, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (17, 1), (34, 1), (41, 1), (45, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (31, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (23, 1), (32, 1), (36, 1), (47, 1), (51, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (26, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (26, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB5
