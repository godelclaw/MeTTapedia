import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_6_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9e66184e9b539d1d0430e694b29dbcd3d6b53b045e53e097498c91acd74e0800"
def certificateSHA256 : String := "8f55f5a560f1075646e21326d456efe82b584cc36120d83a5b35106672b8e009"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 670 := ![
  0,
  1,
  7,
  9,
  10,
  15,
  19,
  23,
  143,
  147,
  162,
  163,
  168,
  170,
  294,
  301,
  315,
  318,
  319,
  323,
  409,
  424,
  437,
  438,
  443,
  449,
  463,
  478,
  479,
  491,
  580,
  657,
  658,
  659,
  663,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(17, 1), (29, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (40, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (49, 1), (67, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (45, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (45, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (47, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (34, 1), (40, 1), (45, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (34, 1), (40, 1), (45, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (34, 1), (40, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (34, 1), (40, 1), (42, 1)] }, { coefficient := -1, powers := [(25, 1), (34, 1), (40, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (30, 1), (54, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (42, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (34, 1), (40, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (34, 1), (40, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (45, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (45, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (30, 1), (48, 1), (54, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_6_2_5.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_6_2_5
