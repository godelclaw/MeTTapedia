import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_2_3_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0b1a05c9b20b1ce4947a30fc808e19e78b1ae21b5fe32a586fd5c99b7409eec6"
def certificateSHA256 : String := "6a7a90e9e813f91c4ae570d61b102911265d3d653268d1113e0e06c8b73cc994"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 614 := ![
  6,
  14,
  18,
  32,
  183,
  202,
  206,
  210,
  306,
  308,
  309,
  311,
  325,
  326,
  330,
  430,
  434,
  441,
  494,
  501,
  552,
  558,
  569,
  570,
  600,
  601,
  602,
  603,
  607,
  609,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(4, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 2, powers := [(11, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := -2, powers := [(15, 1), (35, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (46, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(29, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (43, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (21, 1), (35, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (21, 1), (29, 1), (35, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (15, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (40, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (40, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (44, 2), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (17, 1), (35, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (21, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (21, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (50, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_2_3_5.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_2_3_5
