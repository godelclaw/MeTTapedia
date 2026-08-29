import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB0_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "905a558dd3712e5fc11726dc431ab9f23813b5d5e64cd11fad8221ec6f6bf766"
def certificateSHA256 : String := "636232b32a4956ad6b1cab9bf5a4fe509afc0c37a30d4611186368ae05fe0a35"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 665 := ![
  1,
  14,
  21,
  160,
  162,
  164,
  169,
  173,
  177,
  196,
  238,
  239,
  300,
  306,
  310,
  312,
  313,
  388,
  406,
  435,
  439,
  450,
  469,
  588,
  609,
  655,
  656,
  658,
  660,
  661,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (48, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (41, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (41, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (29, 1), (41, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (41, 1), (48, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (41, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (41, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1), (43, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (48, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (41, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1), (41, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (29, 1), (41, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (29, 1), (41, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(29, 1), (41, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (41, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (29, 1), (41, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (41, 1), (45, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (41, 1), (45, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (29, 1), (41, 1), (47, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (41, 1), (47, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (17, 1), (29, 1), (41, 2), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (29, 1), (41, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (29, 1), (41, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 2), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (41, 1), (45, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB0_3_4.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB0_3_4
