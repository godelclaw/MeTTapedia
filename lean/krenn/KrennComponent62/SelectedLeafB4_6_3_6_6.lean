import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_6_3_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4b4baab39bd0aa221cd356092c327ba7c35e31cadc75590ad24234011c8d778e"
def certificateSHA256 : String := "392faf811075db6a20c8ce1d94f4fca4d8a315f4a459c35edb62a670897ddcad"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 673 := ![
  18,
  146,
  147,
  153,
  154,
  293,
  294,
  296,
  301,
  302,
  311,
  404,
  408,
  440,
  444,
  453,
  454,
  471,
  476,
  484,
  515,
  550,
  557,
  578,
  657,
  658,
  660,
  663,
  667,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1), (52, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1), (58, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (53, 1), (58, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(22, 1), (48, 1), (56, 1), (58, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(24, 1), (30, 1), (41, 1), (45, 1), (50, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (41, 1), (45, 1), (52, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (45, 1), (50, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (45, 1), (52, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (53, 1), (58, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (30, 1), (45, 1), (50, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (45, 1), (52, 1), (60, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (30, 1), (38, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (43, 1), (52, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (44, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (58, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (30, 1), (45, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(24, 1), (30, 1), (45, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (45, 1), (50, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (30, 1), (45, 1), (50, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (58, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (56, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (58, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (30, 1), (46, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (30, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (43, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (52, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (30, 1), (45, 1), (50, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (45, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (30, 1), (46, 1), (52, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (41, 1), (53, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (30, 1), (41, 1), (45, 1), (50, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (41, 1), (45, 1), (52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (58, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (16, 1), (33, 1), (52, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (58, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (56, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (48, 1), (56, 1), (58, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(12, 1), (46, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1), (48, 1), (58, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (16, 1), (22, 1), (52, 1), (58, 1), (68, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (58, 1), (68, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_6_3_6_6.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_6_3_6_6
