import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c224c73b30ebd4233eba5eea1b70db40233f028a10cc457f48aeba735dd40a8d"
def certificateSHA256 : String := "7b95894f3d61da85dd714621796980ddc553ce3d3942bc681bf3e79569afea24"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 667 := ![
  0,
  10,
  11,
  13,
  17,
  19,
  142,
  161,
  167,
  168,
  301,
  318,
  323,
  343,
  432,
  433,
  437,
  440,
  442,
  443,
  449,
  478,
  581,
  584,
  618,
  657,
  658,
  663,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1), (38, 1), (52, 1), (53, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (38, 1), (52, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (38, 1), (52, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(24, 1), (38, 1), (53, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (48, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (45, 1), (52, 2), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (45, 1), (52, 2)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (20, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (49, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (19, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (26, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (29, 1), (38, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (31, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (26, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (38, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (29, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (31, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (26, 1), (38, 1), (60, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB5_6_5.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_6_5
