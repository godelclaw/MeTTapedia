import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB4_7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c24326bfa451fcaade4fc244fd77e8bf76194209d71b0bf7865ce3a67f7f72cb"
def certificateSHA256 : String := "9cdeed9a49a5925c7c1aa1eac3993d5b9f0d6a1dcb27c2aa0d8be22b73822815"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 622 := ![
  12,
  20,
  21,
  28,
  38,
  92,
  201,
  217,
  225,
  241,
  315,
  339,
  340,
  342,
  353,
  399,
  467,
  474,
  509,
  517,
  561,
  578,
  579,
  580,
  581,
  611,
  612,
  614,
  615,
  616,
  617,
  619,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(3, 1), (19, 1), (30, 1), (40, 1), (54, 2)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (30, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (30, 1), (40, 1), (54, 2)] }, { coefficient := 2, powers := [(19, 1), (27, 1), (40, 1), (43, 1)] }, { coefficient := -2, powers := [(19, 1), (33, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (28, 1), (46, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (40, 1), (44, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (4, 1), (19, 1), (30, 1), (40, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (19, 1), (30, 1), (40, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (33, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (4, 1), (19, 1), (30, 1), (40, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (19, 1), (30, 1), (40, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (33, 1), (40, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (19, 1), (25, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (16, 1), (19, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (25, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (33, 1), (40, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (19, 1), (30, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (19, 1), (25, 1), (30, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (25, 1), (30, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (25, 1), (30, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (22, 1), (40, 1), (43, 1)] }, { coefficient := -4, powers := [(19, 1), (23, 1), (25, 1), (40, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (25, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (40, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (40, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (19, 1), (28, 1), (30, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (28, 1), (30, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (28, 1), (30, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := 4, powers := [(19, 1), (23, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (28, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (19, 1), (28, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (28, 1), (30, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (28, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (28, 1), (40, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (19, 1), (28, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (28, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (22, 1), (28, 1), (40, 1), (43, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(19, 1), (28, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (39, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (40, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (4, 1), (19, 1), (28, 1), (30, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (19, 1), (28, 1), (30, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (28, 1), (33, 1), (40, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (28, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1), (44, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1)] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB4_7_6.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB4_7_6
