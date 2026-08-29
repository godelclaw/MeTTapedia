import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2c8670444ed7ad8ecb051336216bc855c3a2ad97819b7faec5fe63a71c07682c"
def certificateSHA256 : String := "6187c53fd777d7a5a94bfe2f30c200a3ed71c542665400e91738c6890a98d6f1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 13 → Fin 668 := ![
  10,
  179,
  194,
  352,
  497,
  579,
  604,
  605,
  654,
  657,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 13 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 13 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (37, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (45, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (45, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (31, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (40, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (34, 1), (40, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (65, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (29, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (31, 1), (40, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (31, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (34, 1), (40, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (34, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (10, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (59, 2)] }, { coefficient := -1, powers := [(3, 1), (40, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (45, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (31, 1), (37, 1), (59, 2)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (31, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (31, 1), (40, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (4, 1), (34, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (31, 1), (37, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (31, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (40, 1), (45, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (10, 1), (34, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (31, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (31, 1), (40, 2), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (31, 1), (40, 2), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (15, 1), (34, 1), (40, 2), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (59, 2)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (23, 1), (59, 2)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (31, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (31, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (34, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (23, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (56, 2)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (34, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (34, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (23, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (31, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (31, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (34, 1), (51, 2)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }]
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
    ¬ ∀ index : Fin 13,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_6_1.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_6_1
