import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3e5c05ad85a5ac6d14b9f903b4fb7a9d0722d8d137c4861cc1eaf8fea8a152e4"
def certificateSHA256 : String := "204d34c4562d80a845c3f28395e2b5d1a72adde7c249c0c2441e34da2b4c0548"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 666 := ![
  0,
  1,
  2,
  3,
  5,
  7,
  10,
  13,
  15,
  19,
  153,
  156,
  160,
  165,
  176,
  253,
  272,
  298,
  305,
  307,
  320,
  327,
  448,
  451,
  453,
  487,
  562,
  662,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (29, 1), (36, 1), (43, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (29, 1), (36, 1), (50, 1), (60, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (13, 1), (29, 1), (36, 1), (60, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (36, 1), (47, 1), (61, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (36, 1), (48, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (23, 1), (36, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (48, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (19, 1), (23, 1), (36, 1), (58, 1), (60, 1), (64, 2)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (24, 1), (38, 1), (43, 1), (50, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (24, 1), (29, 1), (36, 1), (41, 1), (60, 1), (64, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (29, 1), (36, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (32, 1), (36, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (36, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (36, 1), (41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (36, 1), (46, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (29, 1), (36, 1), (53, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (23, 1), (36, 1), (58, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (29, 1), (36, 1), (41, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (36, 1), (43, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (36, 1), (58, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (29, 1), (36, 1), (41, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (38, 1), (50, 1), (52, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (55, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (48, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (38, 1), (50, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (29, 1), (36, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (23, 1), (36, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (36, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (36, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (36, 1), (47, 1), (54, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 2), (36, 1), (48, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (29, 1), (36, 1), (43, 1), (47, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(2, 1), (13, 1), (29, 1), (36, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (23, 1), (36, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (29, 1), (36, 1), (47, 1), (50, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (41, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (24, 1), (38, 1), (43, 1), (50, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (19, 1), (23, 1), (36, 1), (45, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (24, 1), (29, 1), (36, 1), (41, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB7
