import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "838a33b5673c3bbd1deae310be0a87bfdba400af1e2c75ed7e2e69eee97e74f4"
def certificateSHA256 : String := "a165399367db27f4e1341c2cab1bd684ff7de5502bed8105fcb253173b077972"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 668 := ![
  8,
  13,
  15,
  17,
  23,
  24,
  25,
  33,
  170,
  299,
  300,
  301,
  302,
  316,
  325,
  408,
  428,
  436,
  440,
  448,
  468,
  523,
  540,
  571,
  588,
  608,
  609,
  612,
  660,
  661,
  662,
  663,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(4, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (37, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (37, 1), (39, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (39, 1), (43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (11, 1), (37, 1), (43, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (37, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (27, 1), (43, 1), (48, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (48, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (43, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (53, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1), (50, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (48, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1), (48, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (37, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (37, 1), (43, 1), (47, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (37, 1), (43, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (37, 1), (43, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (27, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (43, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (27, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (43, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (27, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (27, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (37, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (11, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (11, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (27, 1), (43, 1), (45, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (43, 1), (45, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (27, 1), (43, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (43, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (28, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (27, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (27, 1), (43, 1), (48, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (43, 1), (48, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (27, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (43, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (28, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (28, 1), (37, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (28, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (28, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (33, 1), (37, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 1), (31, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (26, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (31, 1), (43, 1), (48, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_5
