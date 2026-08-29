import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_2_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "939c547086bd48b67f58e58225e9bd4f9f8e7809ef7296436dfac48fa7dc4d83"
def certificateSHA256 : String := "ffe982dc0c38fddea6f38839a54449f7364ee869f0ebd0c494e742915aebe1a3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 673 := ![
  22,
  28,
  177,
  308,
  349,
  353,
  416,
  420,
  422,
  439,
  456,
  580,
  581,
  583,
  584,
  600,
  601,
  610,
  612,
  644,
  646,
  658,
  661,
  663,
  664,
  668,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (51, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (26, 1), (32, 1), (56, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (21, 1), (51, 1), (58, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (21, 1), (56, 1), (58, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (27, 1), (58, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1), (26, 1), (44, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1), (26, 1), (56, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (26, 1), (43, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (26, 1), (51, 1), (55, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (26, 1), (55, 1), (56, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (27, 1), (55, 1), (61, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (51, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (32, 1), (56, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (26, 1), (44, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (26, 1), (56, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (43, 1), (61, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (32, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (18, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (18, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (43, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (44, 1), (64, 1), (66, 2)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (44, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (18, 1), (55, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (43, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (58, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (26, 1), (55, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (35, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (33, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (36, 1), (58, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (39, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (44, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (41, 1), (44, 1), (50, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (44, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (35, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (35, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (35, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (43, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (44, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(50, 1), (55, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (48, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (44, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (44, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (48, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (48, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (33, 1), (44, 1), (64, 1), (66, 2)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (33, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (25, 1), (26, 1), (32, 1), (56, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (18, 1), (25, 1), (26, 1), (44, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (18, 1), (25, 1), (26, 1), (56, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (25, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (51, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (25, 1), (26, 1), (43, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(55, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 2), (33, 1), (44, 1), (58, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (26, 1), (32, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (33, 1), (41, 1), (44, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (26, 1), (32, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (18, 1), (21, 1), (51, 1), (58, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (18, 1), (21, 1), (56, 1), (58, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (18, 1), (27, 1), (58, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (41, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (16, 1), (18, 1), (26, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (16, 1), (18, 1), (26, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (18, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (18, 1), (26, 1), (43, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (16, 1), (18, 1), (26, 1), (51, 1), (55, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (16, 1), (18, 1), (26, 1), (55, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (18, 1), (27, 1), (55, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (41, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (41, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (18, 1), (26, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (18, 1), (26, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (26, 1), (43, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (41, 1), (50, 1), (64, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_2_6_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_2_6_6
