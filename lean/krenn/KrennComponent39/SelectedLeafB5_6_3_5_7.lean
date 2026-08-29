import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_3_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0474979b82c6ba83edc365e71d36df9f41205e8b4b26c0028cb9797a266467a1"
def certificateSHA256 : String := "0aa8a6cfce8be5ab29fce37cf8a967a871f489d733a142db62b03bdf0cfb72a6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 676 := ![
  14,
  26,
  62,
  82,
  171,
  173,
  187,
  232,
  280,
  300,
  304,
  305,
  426,
  472,
  482,
  502,
  581,
  602,
  603,
  604,
  605,
  659,
  662,
  663,
  669,
  670,
  671,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 72) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (20, 1), (24, 1), (44, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (20, 1), (24, 1), (51, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (24, 1), (30, 1), (36, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (24, 1), (35, 1), (51, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (24, 1), (51, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (30, 1), (36, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (30, 1), (36, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (35, 1), (42, 1), (59, 2), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (56, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (36, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (59, 1), (67, 1), (71, 1)] }, { coefficient := -1, powers := [(30, 1), (51, 1), (67, 1), (71, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (67, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (20, 1), (59, 2), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (30, 1), (39, 1), (59, 1), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (35, 1), (59, 2), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (35, 1), (39, 1), (59, 1), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (35, 1), (56, 1), (59, 1), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (51, 1), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (35, 1), (39, 1), (59, 1), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (51, 1), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(30, 1), (67, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (36, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(26, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (20, 1), (44, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (20, 1), (51, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (30, 1), (36, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (35, 1), (51, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (36, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (30, 1), (36, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (35, 1), (59, 2), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (49, 1), (59, 2), (67, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (51, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (36, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (20, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (10, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (35, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (59, 2), (67, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (39, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (44, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (39, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (39, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (39, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (44, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (51, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 2), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(51, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (35, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (35, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (4, 1), (30, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (10, 1), (20, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (10, 1), (20, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (10, 1), (30, 1), (36, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (20, 1), (35, 1), (59, 2), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (10, 1), (30, 1), (36, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (20, 1), (35, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (30, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (20, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (30, 1), (36, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (30, 1), (36, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (4, 1), (59, 2), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (10, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (10, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (35, 1), (59, 2), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (10, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (35, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (35, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (35, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (39, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (4, 1), (20, 1), (59, 2), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (20, 1), (59, 2), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (6, 1), (30, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (20, 1), (35, 1), (59, 2), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (30, 1), (35, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (30, 1), (35, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (30, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (33, 1), (35, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (7, 1), (30, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (20, 1), (35, 1), (59, 2), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (30, 1), (35, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (30, 1), (35, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (30, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (33, 1), (35, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 2), (59, 2), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (35, 1), (59, 2), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (30, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (35, 1), (59, 2), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (33, 1), (39, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (67, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_3_5_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_3_5_7
