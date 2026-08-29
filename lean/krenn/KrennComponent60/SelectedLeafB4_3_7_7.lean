import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_3_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b56a318c29064796f4a15529d6c01c044d7681ab919663cdb813be7cdff5e26b"
def certificateSHA256 : String := "f98438f58af9ff5294694822764edc1edd09838546528518b0f204613d1972e0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 668 := ![
  10,
  179,
  194,
  352,
  427,
  497,
  579,
  602,
  603,
  604,
  605,
  648,
  654,
  657,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (25, 2), (34, 1), (40, 1), (51, 1), (56, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (51, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 2), (51, 1), (56, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (51, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (56, 1), (57, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(25, 2), (31, 1), (37, 1), (56, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (31, 1), (37, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(28, 1), (45, 1), (69, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (51, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(22, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (51, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (31, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(27, 1), (51, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (31, 1), (37, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (29, 1), (34, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(40, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 2), (34, 1), (40, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (29, 1), (34, 1), (40, 1), (51, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (34, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(22, 1), (29, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 2), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (29, 1), (51, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (29, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 2), (31, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (31, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(27, 1), (29, 1), (51, 1), (69, 1)] }, { coefficient := -1, powers := [(27, 1), (51, 1)] }, { coefficient := -1, powers := [(28, 1), (29, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (51, 1)] }, { coefficient := -1, powers := [(40, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (25, 1), (34, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (25, 1), (34, 1), (40, 1), (51, 2)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (25, 1), (51, 2)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (31, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (34, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (34, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (25, 2), (34, 1), (40, 1), (51, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (34, 1), (40, 1), (51, 2)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (25, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (25, 2), (51, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 2), (31, 1), (37, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (25, 1), (51, 2)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (51, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (31, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (51, 2)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (51, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_3_7_7.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_3_7_7
