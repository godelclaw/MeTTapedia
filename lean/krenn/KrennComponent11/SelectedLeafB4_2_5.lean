import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB4_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ab5244e26a7c03ce95cd1ce42c413b8445707e0c386385c4c5c87fca65836a01"
def certificateSHA256 : String := "ba58b73ba7659913ecd7a7ce34952207c2c1b51871d3ab0bad19976a0b964590"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 672 := ![
  11,
  12,
  13,
  20,
  160,
  186,
  262,
  269,
  328,
  329,
  330,
  341,
  453,
  488,
  662,
  665,
  668,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (47, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (45, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (46, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (46, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 2), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (30, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (36, 1), (39, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB4_2_5.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB4_2_5
