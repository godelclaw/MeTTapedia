import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "39121c0b7553fd55afa63370d3eccb7d82ccce061c00cd2929ef2575f48c1934"
def certificateSHA256 : String := "fb60d657d7d1762733ac88e17b7d74ed76469628aace8e0baf5c4f67add9a50c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 661 := ![
  1,
  2,
  4,
  17,
  18,
  21,
  133,
  172,
  294,
  296,
  315,
  316,
  318,
  322,
  440,
  443,
  453,
  454,
  470,
  471,
  480,
  557,
  609,
  610,
  646,
  657,
  658,
  659,
  660
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (24, 1), (39, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (39, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (33, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (33, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (33, 1), (45, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (24, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (46, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (30, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (34, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (34, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (38, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (39, 1), (41, 1), (43, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (33, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (43, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (24, 1), (34, 1), (35, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (24, 1), (34, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (24, 1), (34, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (34, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (34, 1), (45, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (24, 1), (39, 1), (41, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (24, 1), (39, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (39, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (33, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (33, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (30, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (33, 1), (43, 1), (45, 1), (48, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB3
