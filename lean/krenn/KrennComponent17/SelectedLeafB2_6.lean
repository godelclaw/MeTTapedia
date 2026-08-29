import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3a7d53e10245b5f90aeb6ffd8c7d6c5fbb7c5b4d6664ed49ae734245404ab6c7"
def certificateSHA256 : String := "895c033212a526a2a76a26893fcb786ccc25fa13e603ecbc5516cf0a46c58895"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 608 := ![
  1,
  2,
  3,
  4,
  6,
  9,
  17,
  18,
  32,
  212,
  311,
  325,
  372,
  414,
  424,
  434,
  438,
  441,
  445,
  459,
  465,
  541,
  549,
  572,
  601,
  602,
  603,
  604,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (36, 1), (40, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (36, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (36, 1), (55, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (13, 1), (15, 1), (29, 1), (31, 1), (32, 1), (36, 1), (55, 1), (59, 2)] }, { coefficient := -2, powers := [(13, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (15, 1), (23, 1), (31, 1), (32, 1), (36, 1), (43, 1), (55, 1), (59, 2)] }],
  [{ coefficient := -1, powers := [(5, 2), (15, 1), (31, 1), (32, 1), (35, 1), (36, 1), (55, 1), (59, 2)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (18, 1), (23, 1), (32, 1), (34, 1), (36, 1), (55, 1), (59, 2)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (36, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (23, 1), (32, 1), (36, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (32, 2), (36, 1), (47, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (17, 1), (31, 1), (32, 1), (36, 1), (47, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (18, 1), (32, 2), (36, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (29, 1), (31, 1), (32, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (18, 1), (31, 1), (32, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (18, 1), (32, 1), (34, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (32, 2), (36, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (32, 1), (36, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1), (36, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (32, 1), (36, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (32, 1), (36, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (31, 1), (32, 1), (36, 1), (47, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (15, 1), (31, 1), (32, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (32, 1), (36, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (32, 1), (36, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (32, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (32, 1), (36, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (32, 1), (36, 1), (44, 2), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (36, 1), (40, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (36, 1), (44, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (15, 1), (31, 1), (32, 1), (35, 1), (36, 1), (52, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (15, 1), (23, 1), (31, 1), (32, 1), (36, 1), (43, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (13, 1), (15, 1), (29, 1), (31, 1), (32, 1), (36, 1), (47, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (18, 1), (23, 1), (32, 1), (34, 1), (36, 1), (52, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (36, 1), (40, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (36, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (32, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (31, 1), (32, 1), (36, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (15, 1), (31, 1), (32, 1), (36, 1), (55, 2), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (15, 1), (31, 1), (32, 1), (35, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (18, 1), (29, 1), (31, 1), (32, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (18, 1), (29, 1), (32, 1), (34, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB2_6.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB2_6
