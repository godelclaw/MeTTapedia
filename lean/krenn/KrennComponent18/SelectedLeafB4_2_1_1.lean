import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_2_1_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f572c047c95170899fc26f33d185039cba1783a06da38d7935748920fa87dac4"
def certificateSHA256 : String := "5b30c873a59a9f6264786dee7a3210f08a49e15dfafda1f2900f4b46cb0b5a3f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 670 := ![
  148,
  149,
  151,
  294,
  319,
  323,
  458,
  501,
  502,
  505,
  523,
  580,
  604,
  606,
  607,
  608,
  656,
  658,
  659,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(30, 1), (36, 1), (39, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (36, 1), (39, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (39, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (33, 1), (46, 2), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (36, 1), (42, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 2), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (46, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (22, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (38, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (46, 2), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (42, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (46, 2), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (42, 1)] }, { coefficient := -1, powers := [(22, 1), (46, 1)] }, { coefficient := -2, powers := [(22, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (46, 2)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 2)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (36, 1), (39, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (64, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (33, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (31, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (36, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (38, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (36, 1), (38, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (33, 1), (46, 2)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (31, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (31, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (33, 1), (38, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (36, 1), (38, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (33, 1), (46, 2)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (33, 1), (46, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (36, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (46, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (38, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (38, 1), (46, 2), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (38, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 2), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (33, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (33, 1), (46, 2), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (36, 1), (42, 2), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (45, 1), (46, 2), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (42, 1), (45, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (45, 1), (46, 2), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (45, 1), (46, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 2)] }, { coefficient := 2, powers := [(11, 1), (22, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 2), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (36, 1), (39, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (38, 1), (46, 3)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (38, 1), (46, 2), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 2), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (42, 2)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(15, 1), (22, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 2), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (38, 1), (42, 2), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (38, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 3)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 2), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 2), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (39, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (52, 2)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (38, 1), (46, 2)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (38, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 2)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_2_1_1.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_2_1_1
