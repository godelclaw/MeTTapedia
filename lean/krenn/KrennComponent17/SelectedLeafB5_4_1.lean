import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d543dc75cfcafe79760ee87f3ef0d22d0ddada7bbbe300404a057de140bdfeab"
def certificateSHA256 : String := "799c33d1c2bc7b2576293953d3416044390f51a8ef0de9964402a20092240abb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 611 := ![
  6,
  7,
  18,
  25,
  30,
  32,
  40,
  183,
  202,
  206,
  207,
  210,
  214,
  281,
  285,
  300,
  309,
  311,
  323,
  325,
  327,
  330,
  410,
  415,
  425,
  427,
  430,
  432,
  434,
  441,
  445,
  454,
  480,
  481,
  501,
  549,
  550,
  570,
  571,
  600,
  601,
  603,
  606,
  607,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (43, 1), (55, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (17, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (27, 1), (47, 1), (50, 1)] }, { coefficient := -2, powers := [(25, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(23, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (43, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (55, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (38, 1), (44, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (47, 1), (52, 1)] }, { coefficient := -2, powers := [(27, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (43, 1), (44, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (44, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (38, 1), (43, 1), (44, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (52, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (27, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (25, 1), (38, 1), (43, 1), (44, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (21, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (27, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (22, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (27, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (32, 1), (55, 1), (57, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_4_1.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_4_1
