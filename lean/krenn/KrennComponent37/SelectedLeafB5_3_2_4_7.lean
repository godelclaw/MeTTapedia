import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_2_4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e97a384d6021f2db677d1c0f40e205304cdcaae510362ae050029782ed725fec"
def certificateSHA256 : String := "14f89c6544990e009440bac215dc57d4629dec224abe1d00884324fd734739a5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 673 := ![
  6,
  7,
  14,
  24,
  148,
  167,
  168,
  175,
  179,
  181,
  216,
  279,
  294,
  296,
  297,
  298,
  299,
  316,
  334,
  370,
  438,
  450,
  454,
  476,
  542,
  566,
  605,
  656,
  657,
  658,
  659,
  661,
  666,
  667,
  668,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(36, 1), (55, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (36, 1), (42, 1), (52, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (61, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (61, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (36, 1), (42, 1), (52, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (45, 1), (61, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (22, 1), (36, 1), (42, 1), (52, 1), (70, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (36, 1), (41, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (36, 1), (42, 1), (52, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_2_4_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_2_4_7
