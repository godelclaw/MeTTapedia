import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_2_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d6b1aa9bb510bfee3831dda4c231ad59f820127309f61c1c95c2c09ca591937e"
def certificateSHA256 : String := "241d396198fb83122bfd9a1867171004f9a8a4198b8e7d3a4db6ae395d895584"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 670 := ![
  18,
  19,
  20,
  21,
  97,
  141,
  151,
  158,
  191,
  252,
  294,
  301,
  302,
  318,
  370,
  408,
  441,
  454,
  557,
  600,
  601,
  655,
  657,
  660,
  661,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (13, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (18, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (47, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (22, 1), (28, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (28, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (28, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (13, 1), (22, 1), (34, 1), (58, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (40, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (22, 1), (31, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (18, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (13, 1), (28, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (13, 1), (28, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (34, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (13, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (22, 1), (27, 1), (34, 1), (58, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (27, 1), (40, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (22, 1), (27, 1), (31, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (22, 1), (31, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (13, 1), (22, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (13, 1), (22, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (13, 1), (22, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (13, 1), (22, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (22, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (40, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (9, 1), (22, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (22, 1), (28, 1), (40, 1), (59, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_2_6_3.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_2_6_3
