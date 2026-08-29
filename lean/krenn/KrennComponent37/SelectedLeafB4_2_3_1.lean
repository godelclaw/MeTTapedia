import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_2_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cbc1700ffb5197386a06fae06b8e9607d2a5faf3ea012a39a3c5af4685154712"
def certificateSHA256 : String := "5d22d3da1740757926cef5bafd0567938eda286313046a8beb09e441d2edbbe8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 670 := ![
  23,
  154,
  283,
  294,
  298,
  299,
  312,
  313,
  466,
  505,
  510,
  532,
  580,
  589,
  604,
  605,
  606,
  656,
  658,
  659,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(10, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(10, 1), (44, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (32, 1), (38, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (37, 1), (41, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (52, 1), (65, 1)] }, { coefficient := -2, powers := [(10, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (35, 1), (41, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1), (46, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (22, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (41, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (35, 1), (41, 1), (46, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (41, 1)] }, { coefficient := -1, powers := [(22, 1), (46, 1)] }, { coefficient := -1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1), (41, 2)] }, { coefficient := 1, powers := [(35, 1), (37, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (32, 1), (38, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (37, 1), (41, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (66, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1), (41, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (32, 1), (38, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (37, 1), (41, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (35, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (30, 1), (32, 1), (38, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (35, 1), (37, 1), (41, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(22, 1), (30, 1), (66, 1)] }, { coefficient := -1, powers := [(30, 1), (35, 1), (37, 1), (41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (35, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (37, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (35, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (35, 1), (41, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (37, 1), (41, 2), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (37, 1), (41, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (37, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (35, 1), (41, 2), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (35, 1), (41, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (35, 1), (41, 1), (44, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (44, 1), (46, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (46, 2)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (29, 1), (32, 1), (38, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (35, 1), (37, 1), (41, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (41, 2), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (41, 1), (46, 2)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (41, 2)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1), (41, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (41, 3)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (41, 2), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (41, 2), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1)] }, { coefficient := -1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (37, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (41, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (37, 1), (41, 2)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (37, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (37, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_2_3_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_2_3_1
