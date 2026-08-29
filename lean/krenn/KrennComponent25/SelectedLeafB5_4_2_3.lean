import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_4_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "461bcf82be6619e0ff48c8be5f1e23f909330ac396d9d3b571284838ebb1b3ee"
def certificateSHA256 : String := "c4ac3effaf4bff5a1663467755c21ac02fc9a188d33c8c56892cd4106e44db74"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 668 := ![
  3,
  173,
  352,
  405,
  433,
  449,
  505,
  578,
  604,
  605,
  606,
  643,
  647,
  654,
  656,
  657,
  658,
  660,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(6, 1), (34, 1), (45, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(34, 1), (36, 1), (52, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (34, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (34, 1), (52, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (31, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (66, 1)] }, { coefficient := -1, powers := [(34, 1), (36, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (31, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (31, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (31, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (28, 1), (31, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1), (52, 2)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := -1, powers := [(34, 1), (36, 1), (52, 2)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (34, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1)] }, { coefficient := 1, powers := [(29, 1), (34, 1), (36, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (31, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (31, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (29, 1), (34, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (29, 1), (34, 1), (52, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (29, 1), (34, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (29, 1), (31, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (31, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (31, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (34, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (34, 1), (52, 2), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (31, 1), (40, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (31, 1), (40, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (31, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (31, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (28, 1), (31, 1), (40, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (28, 1), (31, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (36, 1), (52, 2), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (34, 1), (45, 1), (52, 2)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (34, 1), (40, 1), (52, 2)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (40, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1), (45, 1), (52, 2)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (36, 1), (40, 1), (52, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (34, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (31, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (34, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (36, 1), (52, 2)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_4_2_3.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_4_2_3
