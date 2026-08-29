import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c8211a0ad1ccecd6bc9308780195700f755667123f57aa9dc076620c21f8ae73"
def certificateSHA256 : String := "c7d4a5528220bdac5c1648cd3a34212eb811db1b925dcf0b903ed5c1e7a45e58"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 667 := ![
  0,
  1,
  3,
  4,
  171,
  175,
  181,
  257,
  296,
  310,
  393,
  411,
  446,
  447,
  450,
  454,
  484,
  485,
  529,
  555,
  562,
  566,
  567,
  650,
  657,
  658,
  659,
  660,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (37, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (36, 1), (37, 1), (48, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (36, 1), (39, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (36, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (30, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (30, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -2, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (48, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (37, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (30, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_2_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_2_3
