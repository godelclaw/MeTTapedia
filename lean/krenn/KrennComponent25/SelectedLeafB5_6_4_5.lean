import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_6_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8fde8b016f46301d07e2c7d113f33062d5371442734ab0206e0ae5e565f08663"
def certificateSHA256 : String := "dcad85f9f4645b4acbab939f1b71623f730cc895932e26300887a597f891315a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 668 := ![
  3,
  173,
  188,
  352,
  449,
  505,
  579,
  602,
  603,
  604,
  605,
  643,
  647,
  654,
  657,
  658,
  663,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(21, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (14, 1), (34, 1), (45, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (45, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (14, 1), (28, 1), (34, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (24, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (45, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (34, 1), (45, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 2), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (29, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 2), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (31, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (14, 1), (34, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (14, 1), (34, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (34, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (14, 1), (34, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (29, 1), (34, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (29, 1), (34, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (29, 1), (45, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (45, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (24, 2), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (24, 1), (29, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (29, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 2), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (29, 1), (31, 1), (37, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (29, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (24, 1), (52, 2)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (40, 1)] }, { coefficient := -1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (14, 1), (34, 1), (40, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (14, 1), (34, 1), (45, 2), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (24, 1), (52, 2)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (52, 2)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_6_4_5.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_6_4_5
