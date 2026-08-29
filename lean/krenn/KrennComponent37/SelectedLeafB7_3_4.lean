import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB7_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f5baf52df5e5dcfc7a4a143ead8cb841f5667bd190205072d1ae3520d5634cc1"
def certificateSHA256 : String := "623c62641244ada34a51bb09fda52e38b63297b81c1b8e9f6f09037d447a4c0b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 667 := ![
  1,
  3,
  4,
  171,
  181,
  294,
  297,
  312,
  410,
  411,
  430,
  440,
  450,
  454,
  466,
  503,
  562,
  566,
  570,
  646,
  649,
  657,
  658,
  659,
  660,
  662,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (29, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (29, 1), (42, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (42, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (47, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (25, 1), (29, 2), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (28, 1), (29, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (25, 1), (29, 2), (42, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (28, 1), (29, 1), (42, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (42, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1), (44, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1), (42, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (42, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (42, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (25, 1), (29, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (25, 1), (29, 1), (42, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (28, 1), (42, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (30, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (30, 1), (42, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (29, 1), (54, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (29, 1), (42, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (42, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (25, 1), (29, 2), (54, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (29, 1), (54, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (25, 1), (29, 2), (42, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (28, 1), (29, 1), (42, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (42, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (42, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (37, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1), (42, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (53, 1)] }]
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

#print axioms Krenn.Component37.SelectedLeafB7_3_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB7_3_4
