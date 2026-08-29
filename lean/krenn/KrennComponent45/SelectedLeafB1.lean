import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component45.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "39d4b18cf889879c8143df2041c5301469d89f9ca393ae1087b28f888b3f4d8a"
def certificateSHA256 : String := "5aedb20e2f32d6dac4b65f3634f54c276d6a50b4eb0bc43e3d8e845d4d2509af"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 563 := ![
  0,
  1,
  2,
  50,
  51,
  243,
  252,
  253,
  254,
  255,
  267,
  362,
  365,
  379,
  380,
  386,
  388,
  514,
  557,
  559,
  560,
  562
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (31, 1), (39, 1), (56, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (34, 1), (39, 1), (56, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (43, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (44, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (36, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (34, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (31, 1), (39, 1), (43, 1), (56, 1)] }]
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
    (values : Fin 58 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component45.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component45.SelectedLeafB1
