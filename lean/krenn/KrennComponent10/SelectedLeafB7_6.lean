import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f26e493dc9b31f14be0f09ad56c0e3df29a3f44dffb7e76149f934d4d8fffdd0"
def certificateSHA256 : String := "ded4eccf880e9e384383449e8e27ace532154831435f58a8ccf9fba6afdd4e1a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 641 := ![
  0,
  2,
  4,
  5,
  8,
  15,
  24,
  29,
  35,
  162,
  165,
  181,
  189,
  202,
  349,
  350,
  359,
  363,
  364,
  406,
  409,
  466,
  499,
  550,
  634,
  635,
  636,
  638,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (27, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (48, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (27, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (39, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB7_6.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB7_6
