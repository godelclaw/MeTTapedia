import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d3f991dbdf95a4bfd971614ff0aeafadc16809dcf1b0c571b4e0e9c362fdf254"
def certificateSHA256 : String := "2ebf87fac6f8cb6d4a0ba6d6a4f0a50a491dcb53f87c85a58719d24b772872de"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 588 := ![
  0,
  25,
  40,
  54,
  218,
  219,
  255,
  258,
  373,
  384,
  385,
  391,
  408,
  489,
  507,
  523,
  581,
  582,
  583,
  584,
  586,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (47, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (37, 1), (55, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (37, 1), (42, 1), (45, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (37, 1), (45, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (47, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (25, 1), (37, 1), (45, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (52, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (37, 1), (42, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (25, 1), (37, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (37, 1), (42, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (37, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (25, 1), (37, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (37, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (55, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (42, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (23, 1), (37, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (25, 1), (37, 1), (42, 1), (45, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (25, 1), (33, 1), (37, 1), (45, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (33, 1), (37, 1), (47, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (24, 1), (25, 1), (37, 1), (45, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (28, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (28, 1), (52, 1), (59, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB7_1.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB7_1
