import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB4_6_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c87b669531667f69c7f3aae964508b397f9d5c919c95169e45d9f948d2646d49"
def certificateSHA256 : String := "faa2b51a4a9bd62f83e86ab7dc18a84defc7ebbd6014543413d492119f505b5d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 668 := ![
  3,
  173,
  188,
  352,
  505,
  579,
  602,
  603,
  604,
  605,
  654,
  657,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(3, 1), (24, 2), (31, 1), (45, 1), (56, 2), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 2), (31, 1), (52, 1), (56, 2), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 2), (34, 1), (45, 1), (52, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (45, 1), (56, 2), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (52, 1), (56, 2), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (34, 1), (45, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (45, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 2), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (45, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 2), (52, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 2), (31, 1), (37, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(26, 1), (40, 1), (67, 1)] }, { coefficient := -2, powers := [(26, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (31, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (45, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (34, 1), (45, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (45, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (52, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (34, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (29, 1), (31, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (31, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 2), (31, 1), (45, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 2), (31, 1), (52, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 2), (34, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (29, 1), (31, 1), (45, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (29, 1), (31, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (29, 1), (34, 1), (45, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (34, 1), (45, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 2), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (29, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 2), (31, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (31, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1)] }, { coefficient := -1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (24, 1), (31, 1), (45, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (24, 1), (31, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (24, 1), (34, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (24, 1), (31, 1), (45, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (24, 1), (31, 1), (52, 2), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (24, 1), (34, 1), (45, 1), (52, 2)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (24, 1), (52, 2)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (24, 1), (31, 1), (45, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (24, 1), (31, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (24, 1), (34, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (24, 2), (31, 1), (45, 1), (56, 2), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (24, 2), (31, 1), (52, 1), (56, 2), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (24, 2), (34, 1), (45, 1), (52, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (56, 2)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (24, 1), (31, 1), (45, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (24, 1), (31, 1), (52, 2), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (24, 1), (34, 1), (45, 1), (52, 2)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (31, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (31, 1), (56, 2)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (31, 1), (56, 2)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 2)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (24, 2), (52, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 2), (31, 1), (37, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (40, 1)] }, { coefficient := 2, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (24, 1), (52, 2)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (52, 2)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (52, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB4_6_2_7.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB4_6_2_7
