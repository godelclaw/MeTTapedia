import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_6_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "808038d8e197cb5727b9db0d9e0a156c3d502656a1e5902a19cf851df5b386bc"
def certificateSHA256 : String := "771415c04fdbfe8a3a63b6a48913ff524ced669a75685cbaea0ad1e63274c90c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 677 := ![
  4,
  21,
  34,
  147,
  300,
  301,
  317,
  327,
  348,
  585,
  608,
  609,
  660,
  662,
  663,
  672,
  673,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 72) := ![
  [{ coefficient := -1, powers := [(11, 1), (23, 1), (42, 1), (60, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1), (60, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1), (60, 1), (71, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1), (60, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (24, 1), (42, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (53, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (62, 1), (71, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (62, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (60, 1), (71, 1)] }, { coefficient := 1, powers := [(33, 1), (57, 1), (71, 1)] }, { coefficient := 1, powers := [(36, 1), (42, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(42, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }, { coefficient := -1, powers := [(57, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (23, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1), (42, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (23, 1), (31, 1), (42, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (31, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(11, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (60, 1), (61, 1), (71, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [(42, 1), (47, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (60, 1), (61, 1), (71, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (23, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (23, 1), (53, 2)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (53, 2)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (23, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (23, 1), (53, 2)] }, { coefficient := -2, powers := [(11, 1), (21, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (23, 1), (57, 2)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (23, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (23, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (23, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (23, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_6_5_7.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_6_5_7
