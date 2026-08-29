import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5eddca7780531438801a269c833a01a0dac7bdafb1bd90953be273f1bb9279cf"
def certificateSHA256 : String := "05d0586f5e547fb3da4fedb7f7c70a236926bb7add7aea83650a5b3228da1df5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 670 := ![
  187,
  188,
  316,
  319,
  393,
  394,
  413,
  416,
  422,
  439,
  452,
  505,
  532,
  562,
  580,
  581,
  644,
  649,
  663,
  665,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(27, 1), (39, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (24, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1), (42, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (27, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (42, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (24, 1), (27, 1), (42, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (24, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_1
