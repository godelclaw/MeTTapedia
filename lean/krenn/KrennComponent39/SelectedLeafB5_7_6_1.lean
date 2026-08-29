import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_7_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "950a20444e439ce59b7dc492a594921728b4d1022327d0ef55a09cac34f3546c"
def certificateSHA256 : String := "f45dffc6bdf1dda9a0421d5856c3845a950cdabf77e35f6dfe61d40caf705db2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 673 := ![
  184,
  192,
  193,
  277,
  300,
  301,
  316,
  319,
  324,
  396,
  397,
  410,
  419,
  430,
  434,
  452,
  462,
  471,
  566,
  645,
  650,
  660,
  661,
  665,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (40, 1), (51, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (40, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (54, 1)] }, { coefficient := -1, powers := [(27, 1), (40, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (51, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (40, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (40, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (42, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (45, 1), (51, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (49, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1), (45, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (40, 1), (45, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1), (40, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (39, 1), (40, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (39, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_7_6_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_7_6_1
