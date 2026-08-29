import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9908ad27e93bedaa5e7caa73f419d514f84e08216917408ac7969ad86108745b"
def certificateSHA256 : String := "7189ec5950cb08aa3745b491156a157d410e3b50cf57f3a53984d9f33ff2057b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 668 := ![
  0,
  1,
  3,
  6,
  7,
  13,
  15,
  23,
  24,
  30,
  33,
  147,
  173,
  300,
  302,
  316,
  329,
  366,
  408,
  428,
  440,
  448,
  468,
  534,
  571,
  612,
  661,
  663,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (8, 1), (29, 1), (47, 1), (61, 1), (63, 2)] }],
  [{ coefficient := -2, powers := [(13, 1), (31, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (8, 1), (25, 1), (47, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (36, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (23, 1), (25, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (28, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (48, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1), (48, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1), (48, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (17, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (25, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (25, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (8, 1), (47, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (8, 1), (29, 1), (47, 1), (49, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (27, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (16, 1), (23, 1), (25, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (31, 1), (43, 1), (48, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB6_1
