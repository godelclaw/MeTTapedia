import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_6_7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4abb0471b57facdf2210ef31b22259301b732bf9970c1c23e1a835bdb83a402d"
def certificateSHA256 : String := "bbe432b190da7a257d16d378cd1fe48b5101257ecf55157f62b9365cf087df77"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 673 := ![
  187,
  319,
  393,
  422,
  439,
  452,
  462,
  503,
  532,
  580,
  581,
  607,
  644,
  661,
  663,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(18, 2), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (39, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (26, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (26, 1), (39, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (26, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(39, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(45, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (51, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_6_7_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_6_7_5
