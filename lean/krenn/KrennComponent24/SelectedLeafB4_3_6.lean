import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB4_3_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0b51cc29f63311cb02c9672ea8d7f5b915f770f3865111628d299815c08628c0"
def certificateSHA256 : String := "f5086028889d975202478228e6f1f2f75ddf8f8eff466741d40e96607b628337"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 673 := ![
  2,
  11,
  12,
  15,
  16,
  23,
  150,
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
  462,
  471,
  584,
  585,
  598,
  663,
  666,
  668,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (25, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1)] }],
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
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 67) := ![
  [{ coefficient := -2, powers := [(6, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (43, 1), (46, 1), (47, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (31, 1), (43, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (31, 1), (43, 1), (45, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (31, 1), (43, 1), (46, 1), (47, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1), (47, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (55, 1), (65, 1)] }],
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
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(26, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(26, 1), (43, 1)] }, { coefficient := -1, powers := [(43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (31, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(8, 1), (26, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (31, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (31, 1), (43, 1), (46, 1), (47, 1), (63, 1)] }, { coefficient := 2, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (26, 1), (31, 1), (43, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(18, 1), (26, 1), (31, 1), (43, 1), (45, 1), (57, 1)] }, { coefficient := -2, powers := [(18, 1), (26, 1), (31, 1), (43, 1), (46, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (43, 1), (47, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (24, 1), (42, 1), (43, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (30, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (30, 1), (43, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (42, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (42, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (42, 1), (43, 1)] }, { coefficient := 2, powers := [(18, 1), (26, 1), (30, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (43, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB4_3_6.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB4_3_6
