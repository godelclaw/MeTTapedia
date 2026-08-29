import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_2_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c93f472007fc963aecf7b799791e258b752dc6c4d689e1419a29205fad57ad5b"
def certificateSHA256 : String := "7922868407e6e0c2cf559760155b8bc9dd9ed66a7f0cb6281b1b2ed533c3d628"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 648 := ![
  168,
  187,
  194,
  348,
  349,
  400,
  405,
  417,
  517,
  530,
  558,
  579,
  580,
  634,
  637,
  643,
  645,
  646,
  647
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (51, 2), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (37, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (51, 2), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (31, 1), (37, 1), (51, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (34, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (34, 1), (45, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (34, 1), (52, 1), (63, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (37, 1), (58, 2)] }, { coefficient := -1, powers := [(3, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (37, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (45, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (20, 1), (22, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (23, 1), (51, 1), (52, 1), (63, 2)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (52, 1), (63, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (45, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (20, 1), (22, 1), (51, 2), (58, 1)] }, { coefficient := 2, powers := [(3, 1), (22, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (23, 1), (51, 2), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(22, 1), (23, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (37, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (45, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (22, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(20, 1), (22, 1), (23, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (11, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (20, 1), (37, 1), (51, 1), (58, 2)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (58, 2)] }, { coefficient := 1, powers := [(3, 1), (45, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (37, 1), (51, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (51, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (34, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(1, 1), (23, 1), (40, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (31, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (20, 1), (31, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (23, 1), (34, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (34, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (31, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (23, 1), (31, 1), (37, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (23, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (20, 1), (22, 1), (51, 2), (58, 2)] }, { coefficient := -2, powers := [(3, 1), (4, 1), (22, 1), (51, 1), (58, 2)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (34, 1), (37, 1), (58, 2)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (34, 1), (45, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (20, 1), (22, 1), (45, 1), (51, 2), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (11, 1), (22, 1), (45, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (22, 1), (51, 2), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (31, 1), (37, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (34, 1), (37, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (34, 1), (45, 2), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (20, 1), (22, 1), (40, 1), (51, 2), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (16, 1), (22, 1), (40, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (34, 1), (37, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (34, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (22, 1), (23, 1), (51, 2), (52, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(4, 1), (22, 1), (23, 1), (51, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (34, 1), (37, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (23, 1), (45, 1), (51, 2), (52, 1), (63, 1)] }, { coefficient := -2, powers := [(11, 1), (22, 1), (23, 1), (45, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (23, 1), (51, 2), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (31, 1), (37, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (34, 1), (37, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (22, 1), (23, 1), (40, 1), (51, 2), (52, 1), (63, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (23, 1), (40, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (34, 1), (37, 1), (40, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (58, 2)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (20, 1), (37, 1), (58, 2)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (23, 1), (37, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (40, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (45, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (20, 1), (22, 1), (51, 1), (58, 2)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (22, 1), (58, 2)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (34, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (34, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (20, 1), (22, 1), (45, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (22, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (34, 1), (45, 2)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (20, 1), (22, 1), (40, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (34, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (22, 1), (23, 1), (51, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (23, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (40, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (23, 1), (45, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (23, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (22, 1), (23, 1), (40, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (40, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_2_4_1.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_2_4_1
