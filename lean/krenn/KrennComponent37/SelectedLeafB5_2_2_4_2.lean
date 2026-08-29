import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_2_4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "802020dacb1534f510dcaf8ce2aff54ee0f9deaba78289fa1e0ea8be965dc318"
def certificateSHA256 : String := "65a333bbbec90a2c3acdedb23f34eab1fc5fc77005f41f35eef5f9235bdfca4c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 673 := ![
  8,
  17,
  175,
  179,
  180,
  181,
  294,
  295,
  300,
  433,
  438,
  454,
  481,
  566,
  602,
  603,
  655,
  657,
  658,
  660,
  661,
  663,
  664,
  666,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (23, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (21, 1), (23, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (24, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (20, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (21, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 2), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (21, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (34, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (18, 1), (20, 1), (28, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (18, 1), (21, 1), (28, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (28, 1), (34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (24, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (31, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (19, 1), (24, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (24, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (44, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (36, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (36, 1), (48, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (44, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (24, 1), (49, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 2), (24, 1), (48, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (25, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (24, 2), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_2_4_2.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_2_4_2
