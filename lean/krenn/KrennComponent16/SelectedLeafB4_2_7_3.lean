import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB4_2_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c620d90e242dc47e34d6c439ae42a899e14a659134035b62b219ec6f9aebe290"
def certificateSHA256 : String := "e3ea7acf307f846c555ce18ea156258ed9591063a8f2a4a0cb1dee23fedcbc59"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 674 := ![
  10,
  13,
  18,
  23,
  162,
  170,
  302,
  316,
  408,
  436,
  440,
  448,
  595,
  661,
  664,
  667,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (58, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (58, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (50, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (57, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (57, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(50, 1), (55, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (48, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (42, 1), (55, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (47, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (55, 1), (57, 1), (65, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB4_2_7_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB4_2_7_3
