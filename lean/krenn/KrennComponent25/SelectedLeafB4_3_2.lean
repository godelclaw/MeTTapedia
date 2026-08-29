import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB4_3_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "94cba63e89558df960efdc85b622cae9ad9665bd15e27fb2fba3a3af35064ddb"
def certificateSHA256 : String := "9a6404424f2aa14023cb561c8660a10758d36ec68d55ebe08721cc636a245ffd"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 665 := ![
  0,
  1,
  14,
  21,
  70,
  160,
  169,
  188,
  196,
  199,
  300,
  312,
  313,
  430,
  435,
  439,
  450,
  478,
  588,
  600,
  601,
  606,
  653,
  655,
  658,
  659,
  660,
  662,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 65) := ![
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (36, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (24, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (23, 1), (44, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (36, 1), (60, 1)] }, { coefficient := -2, powers := [(23, 1), (36, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (36, 1), (42, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (24, 1), (42, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (23, 1), (42, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }, { coefficient := -1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (16, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (23, 1), (36, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (36, 1), (49, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (36, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (24, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (23, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (23, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (42, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(3, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (8, 1), (23, 1), (33, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (13, 1), (23, 1), (24, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (24, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (33, 1), (36, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (23, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (23, 1), (30, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (18, 1), (23, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (18, 1), (23, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (22, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (28, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (41, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB4_3_2.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB4_3_2
