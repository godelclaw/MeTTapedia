import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_2_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ec9c36bfe0a3a210a1e25bb4bb7461404c6de4b50bc869f1b206564115169eb3"
def certificateSHA256 : String := "50cf00f1e8a801800b3c19548d319fa9f6ef7bcaf26bf6e0b27b59a0cf799a99"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 670 := ![
  0,
  10,
  19,
  246,
  294,
  301,
  318,
  323,
  409,
  437,
  443,
  496,
  497,
  625,
  657,
  660,
  663,
  665,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (31, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (28, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (26, 1), (33, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (33, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (36, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (45, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (45, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (31, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (37, 1), (40, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (33, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (36, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (37, 1), (40, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (37, 1), (40, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (52, 2), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 2), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (31, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (33, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (28, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (33, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (28, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (33, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (36, 1), (52, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (49, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (28, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (33, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (40, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (40, 1), (52, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (40, 1), (52, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (28, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (33, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (36, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (28, 1), (37, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (37, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (37, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (28, 1), (31, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (31, 1), (33, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (31, 1), (36, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (19, 1), (28, 1), (31, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (19, 1), (28, 1), (37, 1), (40, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (19, 1), (31, 1), (33, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (19, 1), (31, 1), (36, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (19, 1), (33, 1), (37, 1), (40, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (19, 1), (36, 1), (37, 1), (40, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (28, 1), (47, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (24, 1), (33, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (36, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (28, 1), (42, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (33, 1), (42, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (36, 1), (42, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (52, 2), (53, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 2), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_2_1_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_2_1_3
