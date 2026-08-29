import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_0_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "811038ccf417af122bf5bf8d605a729f48884238fbeebf63c0978428a89b0cc9"
def certificateSHA256 : String := "f87d54f24de48e9bbc5e949f44a710387261f44e9ad45779755a038c8ab40ccb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 674 := ![
  4,
  6,
  8,
  9,
  21,
  23,
  31,
  148,
  162,
  166,
  167,
  170,
  171,
  175,
  254,
  300,
  301,
  314,
  316,
  318,
  404,
  408,
  433,
  436,
  440,
  454,
  478,
  498,
  501,
  523,
  540,
  571,
  584,
  609,
  610,
  660,
  661,
  663,
  666,
  667,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (30, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (29, 1), (50, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (11, 1), (19, 1), (25, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (25, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(27, 1), (29, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(29, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (29, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (25, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (11, 1), (25, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (11, 1), (25, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (47, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (25, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (25, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (25, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (27, 1), (29, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (25, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (25, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_0_6_4.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_0_6_4
