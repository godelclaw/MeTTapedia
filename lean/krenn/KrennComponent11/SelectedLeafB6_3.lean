import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4997a15c0f0f57cd3fb9377541a3d65c77e55df885c041d93e9877e52db66628"
def certificateSHA256 : String := "8a1f6c08431cc6c56a4d721a73eb63c471c0f3ce2024354b8f3f868b3dfadcbd"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 669 := ![
  4,
  6,
  19,
  25,
  27,
  161,
  179,
  182,
  184,
  286,
  323,
  329,
  341,
  343,
  350,
  557,
  589,
  601,
  614,
  662,
  663,
  664,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (33, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (30, 1), (52, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (59, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (52, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (57, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (52, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (23, 1), (59, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (49, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := -2, powers := [(17, 1), (30, 1), (42, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (42, 1), (53, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (33, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (23, 1), (60, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (28, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(49, 1)] }],
  [{ coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (28, 1), (53, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(42, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (42, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (33, 1), (42, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (23, 1), (42, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(39, 1), (60, 1)] }, { coefficient := -2, powers := [(41, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(42, 1), (47, 1), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(42, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := -2, powers := [(17, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (30, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (30, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (33, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (33, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (23, 1), (24, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (24, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (33, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (23, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (23, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (28, 1), (49, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (30, 1), (42, 1), (52, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (42, 1), (53, 1), (63, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_3
