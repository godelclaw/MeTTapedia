import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_6_0_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "936c907951f0d9634867f10fe5760d652224d1ac1f022a6ad07873d10fb74c85"
def certificateSHA256 : String := "b217469f4bf3a67c4a0a11a38e26c9259856d52ccec295a9984c841e973c2952"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 648 := ![
  90,
  194,
  348,
  349,
  405,
  517,
  530,
  557,
  565,
  579,
  580,
  634,
  636,
  637,
  639,
  640,
  643,
  646,
  647
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(27, 1), (45, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (27, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (27, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (27, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (65, 1)] }, { coefficient := 2, powers := [(22, 1), (25, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (27, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(22, 1), (51, 1)] }, { coefficient := -1, powers := [(27, 1), (60, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(27, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (45, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (27, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (27, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (45, 1), (50, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (34, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (27, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (27, 1), (39, 1), (45, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1), (45, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (27, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (27, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (20, 1), (27, 1), (58, 2), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (25, 1), (27, 1), (58, 2), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (27, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (22, 1), (25, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (27, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (20, 1), (27, 1), (45, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (25, 1), (27, 1), (45, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (20, 1), (27, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (25, 1), (27, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (40, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (27, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (34, 1), (37, 1), (45, 1)] }, { coefficient := -2, powers := [(11, 1), (22, 1), (25, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (45, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (27, 1), (40, 1), (60, 1)] }, { coefficient := -2, powers := [(11, 1), (25, 1), (27, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (27, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (34, 1), (37, 1), (40, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (25, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (27, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (34, 1), (37, 1), (40, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_6_0_7.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_6_0_7
