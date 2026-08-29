import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B1Certificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e06cb0ecca4aea91cd93976226bfc1993490336788764928c388d5b75e6323f0"
def certificateSHA256 : String := "c1ff1f9a03ebb5774ae2669051e700f25c785dd049e5224177dc853a0cd6f256"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 689 := ![
  35,
  61,
  187,
  196,
  215,
  217,
  322,
  330,
  372,
  458,
  470,
  486,
  489,
  495,
  507,
  568,
  650,
  671,
  672,
  674,
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
def selectedEquations : Fin 28 → SparsePoly (Fin 76) := ![
  [{ coefficient := 1, powers := [(13, 1), (72, 1)] }, { coefficient := 1, powers := [(25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (37, 1), (71, 1)] }, { coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (50, 1), (72, 1)] }, { coefficient := 1, powers := [(8, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1)] }, { coefficient := 1, powers := [(22, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (63, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (72, 1)] }, { coefficient := 1, powers := [(23, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (72, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1), (72, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (38, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(33, 1)] }],
  [{ coefficient := 1, powers := [(34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (73, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (75, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 76) := ![
  [{ coefficient := -2, powers := [(15, 1), (37, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (72, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (36, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (45, 1), (69, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (37, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (37, 1), (68, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (48, 1), (53, 1), (75, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1), (75, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (32, 1), (48, 1), (52, 1), (75, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (37, 1), (38, 1), (69, 1), (75, 1)] }],
  [{ coefficient := -1, powers := [(37, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (31, 1), (37, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (38, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (37, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (45, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (27, 1), (36, 1), (65, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(1, 1), (11, 1), (22, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (69, 1), (73, 1)] }, { coefficient := -1, powers := [(9, 1), (28, 1), (66, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (12, 1), (45, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (36, 1), (65, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (50, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (53, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (31, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(22, 1), (31, 1), (37, 1), (69, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (37, 1), (60, 1), (71, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (38, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (38, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (69, 1)] }]
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
    (values : Fin 76 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B1Certificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B1Certificate
