import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB0_3_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fc7c96d390c01cbab92b6e3a3b80dba6e64519e6ab070813ef14d7e5fe78f2bc"
def certificateSHA256 : String := "a6c2fae782835ea3b5b7fbc2168ada695e0222de7c0487ba9e33dcee87b66f49"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 668 := ![
  3,
  11,
  173,
  257,
  352,
  505,
  585,
  586,
  602,
  603,
  604,
  605,
  643,
  654,
  656,
  657,
  661,
  662,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(21, 1), (52, 1), (55, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (45, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (24, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (45, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (45, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (24, 1), (45, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (45, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (52, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1)] }, { coefficient := 1, powers := [(41, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(45, 1), (47, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (45, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (24, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (45, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (40, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (52, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (44, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB0_3_6_5.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB0_3_6_5
