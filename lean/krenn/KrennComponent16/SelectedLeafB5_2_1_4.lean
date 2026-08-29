import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7d4f45bd60c2d4841ef20920088cf0415f3e46ef137a22576cab7188cbd455a8"
def certificateSHA256 : String := "282126b50061228fbe43b06f6ce07cf91891a6d94d4185eb13fc1fe8df303ba4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 674 := ![
  7,
  9,
  13,
  23,
  32,
  142,
  167,
  170,
  171,
  300,
  301,
  314,
  315,
  317,
  321,
  408,
  436,
  440,
  448,
  571,
  573,
  588,
  660,
  661,
  662,
  663,
  667,
  669,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (40, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (36, 1), (50, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (45, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (47, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (21, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (21, 1), (45, 1), (49, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (45, 1), (49, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1), (49, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (49, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (42, 1), (50, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (40, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (34, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (33, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (34, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (23, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (23, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (21, 1), (30, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (30, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (34, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (34, 1), (42, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (34, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (34, 1), (40, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (45, 1), (47, 1), (49, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (48, 1), (49, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (45, 1), (47, 1), (49, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (48, 1), (49, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_1_4.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_1_4
