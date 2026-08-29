import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_2_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1d29cde4cb87b9ee79e6555ed05120d61d7f985b9a1c484f22da1c66bf97349a"
def certificateSHA256 : String := "a4d01a483e88cf4b0d7c3ebddbc6a22238ebd39eae4831350beb044b069c60ec"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 670 := ![
  9,
  15,
  20,
  25,
  26,
  27,
  28,
  150,
  180,
  295,
  301,
  412,
  433,
  450,
  454,
  478,
  516,
  602,
  603,
  612,
  655,
  657,
  658,
  660,
  661,
  663,
  664,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 4, powers := [(13, 1), (20, 1), (24, 1), (55, 1)] }, { coefficient := 2, powers := [(24, 1), (34, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (31, 1), (37, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (30, 1), (51, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (43, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (34, 1), (37, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (24, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (43, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (24, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (24, 1), (34, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (27, 1), (43, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (43, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (27, 1), (34, 1), (37, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (19, 1), (24, 1), (31, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (24, 1), (25, 1), (43, 1), (55, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (24, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (31, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (30, 1), (48, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_2_2_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_2_2_7
