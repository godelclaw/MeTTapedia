import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0a5632eefca195a3190de241c3cd4e9523b1a309687a3e508684fc6ffcc51233"
def certificateSHA256 : String := "dd5f1107a6d1e057cc6cfac629fd4b6c89876baa50ffa0cd2feb861b2d1ab8a1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 611 := ![
  5,
  9,
  19,
  27,
  30,
  32,
  183,
  308,
  309,
  311,
  325,
  434,
  435,
  440,
  445,
  480,
  486,
  504,
  520,
  550,
  569,
  570,
  600,
  601,
  603,
  604,
  606,
  607,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (15, 1), (23, 1), (50, 2), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (36, 1), (44, 1), (50, 2), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (36, 1), (50, 2), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (23, 1), (25, 1), (26, 1), (50, 2), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (26, 1), (50, 1), (51, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (26, 1), (50, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (51, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (23, 1), (25, 1), (36, 1), (50, 3), (58, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (23, 1), (36, 1), (50, 2), (51, 1), (58, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (11, 1), (17, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (23, 1), (36, 1), (50, 2), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (44, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (23, 1), (50, 2), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (23, 1), (26, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (23, 1), (36, 1), (50, 2), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (25, 1), (26, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (25, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (23, 1), (25, 1), (36, 1), (50, 2), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (15, 1), (23, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (23, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (11, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (36, 1), (50, 2), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (26, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (11, 1), (23, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (40, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (44, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (23, 1), (34, 1), (36, 1), (50, 2), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (23, 1), (25, 1), (26, 1), (50, 2), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (17, 1), (23, 1), (26, 1), (50, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (23, 1), (25, 1), (26, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (23, 1), (26, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (21, 1), (23, 1), (25, 1), (36, 1), (50, 3), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (21, 1), (23, 1), (36, 1), (50, 2), (51, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (8, 1), (23, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (15, 1), (23, 1), (31, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (17, 1), (23, 1), (25, 1), (26, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (23, 1), (31, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (23, 1), (25, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (23, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (21, 1), (23, 1), (25, 1), (36, 1), (50, 2), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_2_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_2_4
