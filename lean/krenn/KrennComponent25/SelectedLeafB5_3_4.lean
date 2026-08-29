import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d94447ec684bc96338935fa942efbf30e8fb8ae7a95f8e91f94597e94477f925"
def certificateSHA256 : String := "710ed00c3065c1ced6a5248c996578aafe4410dd6ae90e0c757cbfad7a9ee081"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 665 := ![
  162,
  238,
  306,
  388,
  424,
  434,
  501,
  609,
  658,
  661,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (47, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (28, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (28, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (28, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (18, 1), (32, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (32, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 2), (28, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (19, 1), (28, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (24, 1), (28, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (22, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (28, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (22, 1), (47, 1), (50, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (22, 1), (50, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (50, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_3_4.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_3_4
