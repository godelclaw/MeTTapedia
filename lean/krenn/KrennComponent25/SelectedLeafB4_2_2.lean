import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB4_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9622f83d08246694486d71184a36030805ccd154a40810ce5592d15dd7e30fb8"
def certificateSHA256 : String := "b4dc38aca171c6590758351b309b199aca9359cb43c182b7fc50b2b70e9b3168"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 665 := ![
  0,
  1,
  14,
  21,
  70,
  160,
  169,
  188,
  199,
  300,
  312,
  313,
  430,
  435,
  439,
  450,
  478,
  600,
  601,
  606,
  653,
  655,
  658,
  659,
  660,
  661,
  662,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (36, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (24, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (23, 1), (44, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (36, 1), (60, 1)] }, { coefficient := -2, powers := [(23, 1), (36, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (36, 1), (42, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (24, 1), (42, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (23, 1), (42, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }, { coefficient := -1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (16, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (23, 1), (36, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (36, 1), (49, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (36, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (24, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (23, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (23, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (42, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(3, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (8, 1), (23, 1), (33, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (13, 1), (23, 1), (24, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (24, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (33, 1), (36, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (23, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (23, 1), (30, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (18, 1), (23, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (18, 1), (23, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (22, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (28, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB4_2_2.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB4_2_2
