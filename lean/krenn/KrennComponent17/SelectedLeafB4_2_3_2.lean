import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_2_3_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a36ea780a6618f0f8754cd62f1d49887608e9ce4a669001c67f86ba0bff64bf1"
def certificateSHA256 : String := "6b11792e89fbb3f03d47d76067b103a9b221802e0d63c8b722b7acee68cc447a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 614 := ![
  7,
  8,
  32,
  36,
  41,
  60,
  211,
  306,
  308,
  309,
  325,
  327,
  364,
  434,
  436,
  454,
  486,
  490,
  541,
  549,
  570,
  571,
  600,
  601,
  602,
  603,
  604,
  607,
  609,
  610,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (31, 1), (36, 1), (54, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (36, 1), (55, 1), (57, 2)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (36, 1), (44, 1), (55, 1), (57, 2), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (44, 1), (50, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (44, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (36, 1), (55, 1), (57, 2), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (36, 1), (50, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (36, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (55, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (36, 1), (43, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (54, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (32, 1), (36, 1), (54, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (44, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (36, 1), (55, 1), (57, 2), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (50, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (36, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (34, 1), (36, 1), (37, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := -1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (32, 1), (36, 1), (50, 1), (54, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (37, 1), (55, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (40, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (44, 1), (54, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (38, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (26, 1), (32, 1), (36, 1), (55, 1), (57, 2)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (36, 1), (50, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (26, 1), (32, 1), (36, 1), (44, 1), (55, 1), (57, 2)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (34, 1), (36, 1), (37, 1), (55, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (26, 1), (32, 1), (36, 1), (44, 2), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (34, 1), (36, 1), (37, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (36, 1), (40, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (34, 1), (36, 1), (37, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (36, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (43, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (36, 1), (43, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (47, 1), (57, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_2_3_2.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_2_3_2
