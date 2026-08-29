import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_3_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7460caa3c0c75741a04d2fe92809c834983430a743ff7c5c77e79f278e0b210e"
def certificateSHA256 : String := "0267de2343d34f905c55473e3e525292e647745dd881fff0a03fe0e755e3232b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 677 := ![
  21,
  34,
  147,
  273,
  300,
  301,
  317,
  512,
  608,
  609,
  660,
  662,
  663,
  670,
  672,
  673,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(11, 1), (45, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (42, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(33, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(36, 1), (42, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(42, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }, { coefficient := -1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (31, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(11, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [(42, 1), (47, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_3_5_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_3_5_3
