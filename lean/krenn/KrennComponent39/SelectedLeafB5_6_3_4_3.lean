import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_3_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0fac69d148abcafcd545295c545f40eee97252912413420f62fe6733dfdb76dc"
def certificateSHA256 : String := "3486927de6c3cacd38325d762fa77635cecec02c6281190f447d202c2c681e01"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 676 := ![
  14,
  26,
  171,
  232,
  280,
  304,
  305,
  352,
  391,
  601,
  603,
  658,
  659,
  662,
  667,
  669,
  671,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (42, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (42, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (39, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(39, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (44, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (33, 1), (36, 1), (38, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (29, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (18, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (33, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (23, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (18, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }]
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
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_3_4_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_3_4_3
