import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B3Certificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fa97a84a4a5c09221e712360145cf6bb6de3b870546c82fae77ced5bbb1dd81d"
def certificateSHA256 : String := "25d129400051be3e4cfa2cfa7a56c238ad9772320219f970f4522247bba2b1d7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 689 := ![
  71,
  133,
  187,
  197,
  214,
  215,
  217,
  304,
  322,
  330,
  368,
  507,
  540,
  568,
  586,
  650,
  671,
  672,
  678,
  679,
  680,
  681,
  682,
  684,
  687,
  688
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 77) := ![
  [{ coefficient := 1, powers := [(25, 1), (32, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (65, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (49, 1), (71, 1)] }, { coefficient := 1, powers := [(8, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (50, 1), (71, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (72, 1)] }, { coefficient := 1, powers := [(23, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (33, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (71, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (72, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1), (72, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(33, 1)] }],
  [{ coefficient := 1, powers := [(34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (73, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (75, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (76, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 77) := ![
  [{ coefficient := 1, powers := [(9, 1), (69, 1), (75, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (75, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (27, 1), (49, 1), (72, 1), (73, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (22, 1), (27, 1), (49, 1), (72, 1), (73, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (49, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (72, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (72, 1), (75, 1)] }, { coefficient := 1, powers := [(23, 1), (69, 1), (75, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (72, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (36, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (45, 1), (69, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (49, 1), (72, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(37, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (27, 1), (50, 1), (72, 1), (73, 1), (76, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (27, 1), (49, 1), (65, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (27, 1), (49, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (47, 1), (49, 1), (50, 1), (72, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (45, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (27, 1), (36, 1), (65, 1), (72, 1), (73, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (30, 1), (50, 1), (72, 1), (73, 1), (76, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (50, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(1, 1), (11, 1), (22, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (27, 1), (49, 1), (65, 1), (72, 1), (73, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (15, 1), (27, 1), (49, 1), (71, 1), (72, 1), (73, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (22, 1), (27, 1), (49, 1), (65, 1), (72, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (12, 1), (45, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (36, 1), (65, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (50, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (25, 1), (32, 1), (69, 1), (75, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (32, 1), (48, 1), (75, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (53, 1), (69, 1)] }, { coefficient := -2, powers := [(15, 1), (37, 1), (72, 1)] }, { coefficient := -1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (44, 1), (49, 1), (50, 1), (72, 1), (73, 1)] }]
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
    (values : Fin 77 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B3Certificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B3Certificate
