import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "24f2c719f6f736dafe27a3b2cbf6718137e35f88fa8196fe65cca27e308308d6"
def certificateSHA256 : String := "877a526b7abc7130145d1487ef0c24673d05f0ccec775b1ad5b7ed28cfdb18bf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 673 := ![
  14,
  17,
  26,
  232,
  270,
  280,
  304,
  305,
  318,
  476,
  478,
  511,
  513,
  515,
  602,
  603,
  659,
  662,
  664,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (28, 1), (44, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (33, 1), (36, 1), (66, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (44, 1), (53, 1), (63, 1), (69, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (53, 1), (63, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (33, 1), (36, 1), (53, 1), (63, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1), (42, 1), (56, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (69, 1)] }, { coefficient := 2, powers := [(14, 1), (28, 1), (42, 1), (51, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (42, 1), (56, 1), (66, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (28, 1), (44, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (33, 1), (36, 1), (66, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (44, 1), (53, 1), (63, 1), (69, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1), (63, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (53, 1), (63, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (28, 1), (56, 1), (66, 1), (69, 1)] }, { coefficient := -2, powers := [(14, 1), (28, 1), (51, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (56, 1), (66, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (44, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (69, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (53, 1), (63, 1), (69, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (63, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (56, 1), (66, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (26, 1), (44, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (53, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (44, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (36, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(28, 1), (33, 1), (36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1), (44, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (53, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (53, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (44, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(25, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (28, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (28, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1), (53, 1), (56, 1), (63, 1), (69, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1), (53, 1), (63, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (44, 1), (56, 1), (63, 1), (69, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (56, 1), (57, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (50, 1), (63, 1), (69, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (51, 1), (69, 1)] }, { coefficient := -1, powers := [(28, 1), (45, 1), (53, 1), (56, 1), (66, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (33, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (33, 1), (44, 1), (69, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (44, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (53, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (27, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (28, 1), (44, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (33, 1), (36, 1), (53, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (28, 1), (30, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (28, 1), (44, 1), (69, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (69, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (28, 1), (51, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (28, 1), (56, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (25, 1), (27, 1), (53, 1), (69, 1)] }],
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_3_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_3_7
