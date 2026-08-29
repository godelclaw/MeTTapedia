import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6f1a58eb41f85e5afc4174ff00ce969aa81b1275a929c6ffcdbdcd9fcd75f0ed"
def certificateSHA256 : String := "64cab0814bad8d96e58a284861b8448f17c53c3286894d72e5d9a9ebe6dfee1b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 608 := ![
  1,
  2,
  4,
  6,
  18,
  22,
  32,
  33,
  34,
  42,
  183,
  212,
  213,
  309,
  311,
  325,
  340,
  374,
  415,
  423,
  434,
  441,
  459,
  465,
  466,
  541,
  552,
  572,
  601,
  602,
  603,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (35, 1), (36, 1), (50, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (35, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (31, 1), (35, 1), (36, 1), (38, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (34, 1), (35, 1), (36, 1), (38, 1), (50, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (25, 1), (41, 1), (45, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (45, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (41, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (15, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (13, 1), (35, 1), (38, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (13, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (35, 1), (36, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (35, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (25, 1), (41, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (25, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (35, 1), (38, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (35, 1), (36, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (25, 1), (41, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (41, 1), (43, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (25, 1), (41, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (41, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (25, 1), (41, 1), (45, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (41, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (13, 1), (26, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (31, 1), (35, 1), (36, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (34, 1), (35, 1), (36, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (25, 1), (41, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (41, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (29, 1), (41, 1), (45, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB7_1.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB7_1
