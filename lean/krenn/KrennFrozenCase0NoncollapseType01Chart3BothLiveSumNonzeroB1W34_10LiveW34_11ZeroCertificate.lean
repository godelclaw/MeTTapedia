import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10LiveW34_11ZeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6c771421c97fb4146af707f725e45c8b4417cb72b02a4fcca3162c4d8b2d9515"
def certificateSHA256 : String := "010bc7c70f1d7da3cb82f3ace198247414367349b17ffc96809599f80f38496f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 686 := ![
  205,
  214,
  215,
  217,
  304,
  330,
  368,
  492,
  494,
  495,
  504,
  525,
  568,
  641,
  656,
  671,
  676,
  677,
  678,
  680,
  681,
  682,
  683,
  684,
  685
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 75) := ![
  [{ coefficient := 1, powers := [(37, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (49, 1), (71, 1)] }, { coefficient := 1, powers := [(8, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (50, 1), (71, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (72, 1)] }, { coefficient := 1, powers := [(30, 1), (32, 1), (63, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (72, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1), (72, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(33, 1)] }],
  [{ coefficient := 1, powers := [(34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (73, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (74, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 75) := ![
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (22, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (45, 1), (69, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (49, 1), (72, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (66, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (37, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(66, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(15, 1), (37, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (45, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (27, 1), (50, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(1, 1), (11, 1), (22, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (49, 1), (65, 1), (72, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (12, 1), (45, 1), (57, 1), (69, 1)] }, { coefficient := -1, powers := [(9, 1), (50, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (48, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (32, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (30, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (15, 1), (37, 1), (72, 1)] }]
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
    (values : Fin 75 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10LiveW34_11ZeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10LiveW34_11ZeroCertificate
