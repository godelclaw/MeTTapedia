import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dd0fb91959d1c34e6a9848eca26a9424e5cfd04c1e4fe83682072d41c301ea8d"
def certificateSHA256 : String := "818ac14002a850446483cc77b4e8fa76495148e584bed0ee529cae82034a9612"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 608 := ![
  0,
  1,
  2,
  3,
  4,
  7,
  13,
  27,
  189,
  230,
  311,
  312,
  325,
  378,
  499,
  541,
  553,
  567,
  599,
  601,
  603,
  604,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (32, 1), (36, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (20, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (32, 1), (36, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1), (36, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (36, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (36, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (19, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (42, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (32, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(41, 1), (55, 1)] }, { coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (24, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (19, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (32, 1), (36, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (9, 1), (19, 1), (32, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (32, 1), (33, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (14, 1), (19, 1), (24, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (24, 1), (30, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB6_0.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB6_0
