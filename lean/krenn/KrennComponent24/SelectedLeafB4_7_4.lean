import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB4_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fc86a35b0e9e7ed3183f73598b615f987fd39f30e5fe3e2dfbecf6b6938b445e"
def certificateSHA256 : String := "6634fee6b0fdc0476e38e5610a999849840cf8dd48271a9d57df43395b0e8244"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 673 := ![
  4,
  11,
  12,
  15,
  16,
  23,
  50,
  132,
  150,
  161,
  164,
  282,
  307,
  323,
  365,
  452,
  457,
  462,
  471,
  525,
  598,
  608,
  609,
  610,
  611,
  662,
  663,
  665,
  666,
  667,
  668,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (25, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(19, 1), (28, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(19, 1), (36, 1), (39, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (49, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (49, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1), (47, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (19, 1), (36, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (19, 1), (36, 1), (43, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (19, 1), (36, 1), (43, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (28, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (22, 1), (43, 1), (46, 1)] }, { coefficient := -4, powers := [(19, 1), (23, 1), (26, 1), (43, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (43, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (36, 1), (39, 1), (43, 1)] }, { coefficient := 2, powers := [(19, 1), (27, 1), (43, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 4, powers := [(19, 1), (23, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (36, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (31, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (31, 1), (43, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (22, 1), (31, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(19, 1), (31, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (43, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (19, 1), (31, 1), (36, 1), (43, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1), (47, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (19, 1), (31, 1), (42, 1), (43, 1)] }, { coefficient := -2, powers := [(4, 1), (19, 1), (31, 1), (33, 1), (43, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (23, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (43, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB4_7_4.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB4_7_4
