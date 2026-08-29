import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4ef97985e58d9a415e48b0380d32ccc57d6bd60c0e461c9cff63dbe92933d0c1"
def certificateSHA256 : String := "e84f56305f303e5aafb69339f0abd882c28498d23b4643978cc6c6e509acaf15"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 611 := ![
  6,
  18,
  19,
  21,
  27,
  32,
  37,
  205,
  222,
  308,
  309,
  311,
  325,
  339,
  434,
  438,
  441,
  445,
  480,
  501,
  569,
  570,
  600,
  601,
  603,
  606,
  607,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (44, 1), (50, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (21, 1), (35, 1), (40, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (21, 1), (35, 1), (44, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (26, 1), (35, 1), (40, 1), (44, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (26, 1), (35, 1), (44, 2), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (35, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (35, 1), (44, 1), (46, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (38, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (35, 1), (44, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (44, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (35, 1), (44, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (21, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (26, 1), (35, 1), (44, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (44, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (40, 1), (44, 1), (52, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (40, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (40, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (40, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (20, 1), (21, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (20, 1), (21, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (20, 1), (26, 1), (35, 1), (40, 1), (44, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (20, 1), (26, 1), (35, 1), (44, 2), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (21, 1), (35, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (26, 1), (35, 1), (44, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (35, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }]
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

#print axioms Krenn.Component17.SelectedLeafB5_6_6.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_6
