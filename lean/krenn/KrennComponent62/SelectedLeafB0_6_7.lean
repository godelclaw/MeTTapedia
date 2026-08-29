import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB0_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bcf466408a5b9705fc87cacd06133ab392dbe374424f3300c1391c68b6e1cc53"
def certificateSHA256 : String := "2530bc717775825e82df5f4ea9f198ee8b9e30d64fc5a3bab68e4c34a634fd69"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 667 := ![
  18,
  21,
  54,
  83,
  97,
  135,
  141,
  151,
  158,
  160,
  187,
  301,
  302,
  318,
  454,
  557,
  589,
  657,
  658,
  660,
  661,
  662,
  663,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (53, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (43, 1), (59, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (13, 1), (59, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (53, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (43, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (22, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (22, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (22, 1), (53, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB0_6_7.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB0_6_7
