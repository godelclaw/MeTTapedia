import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB4_2_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9e5d6be5dde6f3ce85a9121921795c0de809e4686b0c807910fd512d5147e7f2"
def certificateSHA256 : String := "59e743ff939a30a51e0640165d455f341b946221197b7def3d7931dc12025a21"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 668 := ![
  3,
  173,
  188,
  352,
  505,
  579,
  585,
  602,
  603,
  604,
  605,
  654,
  657,
  662,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(3, 1), (24, 2), (34, 1), (45, 1), (52, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (34, 1), (45, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (45, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 2), (52, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (55, 1), (56, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 2), (31, 1), (37, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (56, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (45, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (34, 1), (45, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (34, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (45, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 2), (34, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (29, 1), (34, 1), (45, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (34, 1), (45, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 2), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (29, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 2), (31, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [(40, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (24, 1), (34, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (24, 1), (34, 1), (45, 1), (52, 2)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (24, 1), (52, 2)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (40, 1)] }, { coefficient := -1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (24, 1), (34, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (24, 2), (34, 1), (45, 1), (52, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (24, 1), (34, 1), (45, 1), (52, 2)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (24, 2), (52, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 2), (31, 1), (37, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (24, 1), (52, 2)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (52, 2)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB4_2_6_5.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB4_2_6_5
