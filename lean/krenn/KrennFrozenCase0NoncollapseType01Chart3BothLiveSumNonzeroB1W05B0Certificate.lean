import KrennSparseCertificate

/-!
A selected-row reflection of the strict frozen certificate for the B1
`w_05_02 = w_05_22 = 0` leaf.  The semantic bridge supplies the route from
these rows to the canonical chart-3 system.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B0Certificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ca75a4da0ef1b2ac9f0fffa9aa69a41db564eb6301a4b879a272b00a97e8f9a4"
def certificateSHA256 : String := "df6b99fdec8940cbc09861a36fac4691a26d6de99e641472b436fcae147297ce"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 689 := ![
  35,
  188,
  196,
  215,
  304,
  330,
  368,
  525,
  568,
  641,
  650,
  671,
  677,
  678,
  680,
  681,
  682,
  684,
  687,
  688
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 75) := ![
  [{ coefficient := 1, powers := [(13, 1), (72, 1)] }, { coefficient := 1, powers := [(25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (37, 1), (71, 1)] }, { coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (49, 1), (71, 1)] }, { coefficient := 1, powers := [(8, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (50, 1), (71, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (72, 1)] }, { coefficient := 1, powers := [(30, 1), (32, 1), (63, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (72, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1), (72, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(33, 1)] }],
  [{ coefficient := 1, powers := [(34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (73, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 75) := ![
  [{ coefficient := -1, powers := [(15, 1), (37, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (45, 1), (69, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (49, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(9, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (45, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (27, 1), (50, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(1, 1), (11, 1), (22, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (49, 1), (65, 1), (72, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (12, 1), (45, 1), (57, 1), (69, 1)] }, { coefficient := -1, powers := [(9, 1), (50, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (32, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (36, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (42, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1), (60, 1), (71, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 75 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B0Certificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B0Certificate
