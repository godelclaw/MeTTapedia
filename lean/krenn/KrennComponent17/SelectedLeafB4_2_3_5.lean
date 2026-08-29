import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_2_3_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e5920ad3258dd962f50442ae5fa5d3ed7208877e3bdb1af7b9b4abe3dbd285c1"
def certificateSHA256 : String := "a94a69419208fb47a26d7d1355b3558b3c1cedabe46f656b394facb1d7a7a00d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 614 := ![
  6,
  14,
  18,
  32,
  183,
  202,
  214,
  297,
  306,
  308,
  309,
  311,
  325,
  326,
  434,
  441,
  494,
  501,
  558,
  569,
  570,
  600,
  601,
  603,
  604,
  607,
  609,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (55, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (46, 1), (55, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(29, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (43, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (35, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (29, 1), (35, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (40, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (40, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (44, 2), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (44, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (35, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (21, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (50, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_2_3_5.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_2_3_5
