import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bc90e740eba7943ce346c369816eb212bac1b71968b5c0ecb13ed263e78dd9d4"
def certificateSHA256 : String := "e92b662d68441bebcb2148f8d70666ed6e9a858f819d70d7b0cf80050827fe4c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 667 := ![
  9,
  10,
  11,
  15,
  17,
  19,
  143,
  147,
  167,
  301,
  318,
  343,
  409,
  433,
  437,
  438,
  443,
  478,
  479,
  585,
  657,
  659,
  662,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (40, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (26, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (37, 1), (40, 1), (59, 1), (65, 2)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1), (65, 2)] }, { coefficient := -1, powers := [(14, 1), (37, 1), (40, 1), (65, 2)] }, { coefficient := -1, powers := [(24, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (21, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (14, 1), (25, 1), (34, 1), (40, 1), (47, 1), (59, 1), (65, 2)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (40, 1), (60, 1), (65, 2)] }, { coefficient := -2, powers := [(14, 1), (24, 1), (25, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (45, 1), (54, 1), (65, 2)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1), (60, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(14, 1), (17, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (40, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (17, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (31, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (14, 1), (34, 1), (40, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(14, 1), (24, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (49, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (14, 1), (40, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (24, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (40, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (40, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (35, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (34, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (18, 1), (25, 1), (34, 1), (40, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (65, 1)] }, { coefficient := -2, powers := [(14, 1), (18, 1), (24, 1), (25, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (31, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (14, 1), (37, 1), (40, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (17, 1), (25, 1), (34, 1), (40, 1), (47, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (31, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (37, 1), (40, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (23, 1), (40, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (24, 1), (25, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (24, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (29, 1), (40, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_4_5.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_4_5
