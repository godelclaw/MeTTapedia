import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_3_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "520a35cb41c998880cb8a42117a84c87d94ea4759c9f2f905f07ae6693065b5e"
def certificateSHA256 : String := "bb19caebc8193b683def8228a8ac2547dbd1ff308894f71a10905a694465e62d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 673 := ![
  2,
  11,
  13,
  15,
  16,
  23,
  129,
  160,
  161,
  164,
  176,
  281,
  282,
  307,
  321,
  323,
  324,
  452,
  457,
  461,
  462,
  471,
  503,
  504,
  584,
  585,
  598,
  663,
  665,
  668,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 69) := ![
  [{ coefficient := -2, powers := [(6, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (49, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (22, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (43, 1), (46, 1), (47, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (38, 1), (53, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (38, 1), (57, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (67, 1)] }, { coefficient := 2, powers := [(26, 1), (31, 1), (43, 1), (45, 1), (53, 1), (67, 1)] }, { coefficient := 2, powers := [(26, 1), (31, 1), (43, 1), (45, 1), (57, 1), (67, 1)] }, { coefficient := 2, powers := [(26, 1), (31, 1), (43, 1), (46, 1), (47, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (49, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (48, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1), (47, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (42, 1), (43, 1)] }, { coefficient := -2, powers := [(18, 1), (26, 1), (42, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (19, 1), (43, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (43, 1), (53, 1)] }, { coefficient := -2, powers := [(31, 1), (43, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (18, 1), (43, 1)] }, { coefficient := 2, powers := [(18, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := -2, powers := [(26, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := -2, powers := [(26, 1), (43, 1)] }, { coefficient := -1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (31, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(8, 1), (26, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (31, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (31, 1), (43, 1), (46, 1), (47, 1), (65, 1)] }, { coefficient := 2, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (26, 1), (31, 1), (43, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(18, 1), (26, 1), (31, 1), (43, 1), (45, 1), (57, 1)] }, { coefficient := -2, powers := [(18, 1), (26, 1), (31, 1), (43, 1), (46, 1), (47, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (43, 1), (47, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (24, 1), (42, 1), (43, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (30, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (30, 1), (43, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (42, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (42, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (42, 1), (43, 1)] }, { coefficient := 2, powers := [(18, 1), (26, 1), (30, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (43, 1), (65, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_3_6.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_3_6
