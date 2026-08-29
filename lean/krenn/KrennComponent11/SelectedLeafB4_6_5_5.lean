import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB4_6_5_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "38fd0e5728a8782a2a125528a206a8616d5ee7ce7d8f5cf704dbea527c13fbb5"
def certificateSHA256 : String := "b2234e6a3173ff33faa12f8b3256df6c92eee9dd43a9fd039c167666fbdf88e9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 675 := ![
  6,
  8,
  11,
  12,
  20,
  28,
  29,
  165,
  283,
  328,
  329,
  330,
  341,
  453,
  507,
  613,
  661,
  662,
  664,
  665,
  666,
  668,
  670,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (33, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := 2, powers := [(17, 1), (32, 1), (39, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (35, 1), (39, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (35, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (36, 1), (39, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (30, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (39, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (32, 1), (46, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (35, 1), (41, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (35, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (39, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (36, 1), (39, 1), (41, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (35, 1), (38, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (36, 1), (38, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (35, 1), (38, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (36, 1), (38, 1), (39, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (35, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (23, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (32, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (35, 1), (41, 1), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (35, 1), (38, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (35, 1), (38, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (35, 1), (51, 1), (52, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (35, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (17, 1), (35, 1), (39, 1)] }, { coefficient := -2, powers := [(15, 1), (17, 1), (35, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (35, 1), (52, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (38, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (38, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (23, 1), (35, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (21, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (32, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (30, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (21, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (32, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (21, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (30, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (30, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (35, 1), (36, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (35, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (30, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (30, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (30, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (35, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (30, 1), (32, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (30, 1), (35, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (30, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (32, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (35, 1), (36, 1), (39, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (12, 1), (30, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (35, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (30, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (35, 1), (36, 1), (38, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (46, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB4_6_5_5.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB4_6_5_5
