import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_0_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3c2f94c73d1c3bcde3cd29d1495ed5f568c9872d52a309f7e1d3e38fb5839e51"
def certificateSHA256 : String := "3c0d13b39f3c93c365b94af05357cba59bb44a0ee0d3582e8e88075f35911cf7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 674 := ![
  4,
  7,
  8,
  13,
  21,
  31,
  32,
  142,
  166,
  168,
  171,
  176,
  300,
  301,
  314,
  316,
  318,
  321,
  323,
  404,
  434,
  436,
  438,
  448,
  501,
  523,
  540,
  571,
  585,
  609,
  610,
  660,
  661,
  663,
  667,
  669,
  670,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (30, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (25, 1), (47, 1), (61, 1)] }, { coefficient := -2, powers := [(11, 1), (25, 1), (39, 1), (61, 1)] }, { coefficient := 2, powers := [(16, 1), (25, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (11, 1), (19, 1), (25, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (25, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (11, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (33, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (45, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (25, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (25, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (11, 1), (25, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (11, 1), (25, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (25, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (11, 1), (25, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(8, 1), (25, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (47, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := 2, powers := [(1, 1), (8, 1), (25, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (34, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (40, 1), (61, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (25, 1), (33, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (33, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (23, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (8, 1), (25, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (34, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (25, 1), (42, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (25, 1), (47, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (25, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (34, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (45, 1), (49, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_0_4.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_0_4
