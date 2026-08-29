import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0b98b42a7a1be4d725d3f0c870f220426cb03d7d3d8fffbc780b41da5d2b9112"
def certificateSHA256 : String := "fe00f9310791c8fd3037cbb913dfab4c4dc650603db7e5ec3fd51113be48d82f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 667 := ![
  168,
  171,
  175,
  176,
  179,
  180,
  181,
  256,
  279,
  280,
  294,
  295,
  296,
  297,
  307,
  310,
  311,
  316,
  393,
  431,
  433,
  438,
  446,
  450,
  454,
  476,
  482,
  562,
  567,
  657,
  658,
  660,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 65) := ![
  [{ coefficient := -2, powers := [(24, 1), (44, 1), (46, 1)] }, { coefficient := -2, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(24, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (47, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (25, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (28, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (47, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (29, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (20, 1), (24, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (36, 1), (39, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (25, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_2_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_2_4
