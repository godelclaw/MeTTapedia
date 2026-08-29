import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB4_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "13437a5bb24012a64f8dd7f09d72a353f7cb2cd57fd3623742b9d6eaa6580a03"
def certificateSHA256 : String := "73408bf5520b0819dc823c5780dfe6b54fb114c217882e196eeb7e3fd32fe61f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 622 := ![
  12,
  14,
  29,
  30,
  31,
  33,
  38,
  192,
  195,
  220,
  225,
  241,
  339,
  340,
  342,
  353,
  366,
  399,
  438,
  467,
  474,
  509,
  517,
  573,
  578,
  579,
  580,
  581,
  611,
  612,
  613,
  614,
  615,
  617,
  620,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 64) := ![
  [{ coefficient := -2, powers := [(3, 1), (19, 1), (25, 1), (33, 1), (40, 1), (43, 1), (50, 1), (54, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (33, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (22, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (33, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (27, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (19, 1), (25, 1), (28, 1), (33, 1), (40, 1), (43, 1), (50, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (22, 1), (28, 1), (40, 1), (43, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (28, 1), (33, 1), (36, 1), (40, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (28, 1), (40, 1), (50, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (27, 1), (28, 1), (40, 1), (43, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (27, 1), (28, 1), (40, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (33, 1), (36, 1), (40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (51, 1), (54, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (51, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(25, 1), (28, 1), (46, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (40, 1), (44, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (54, 2), (55, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(14, 1), (28, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (52, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (19, 1), (28, 1), (40, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (28, 1), (40, 1), (50, 1), (63, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (28, 1), (40, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (55, 1)] }, { coefficient := 2, powers := [(28, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (19, 1), (33, 1), (40, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (19, 1), (33, 1), (40, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (28, 1), (40, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (19, 1), (25, 1), (33, 1), (40, 1), (43, 1), (50, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (33, 1), (40, 1), (43, 1)] }, { coefficient := -2, powers := [(19, 1), (22, 1), (40, 1), (43, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (40, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (27, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1)] }, { coefficient := -2, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (19, 1), (28, 1), (33, 1), (40, 1), (43, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (28, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (28, 1), (40, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (19, 1), (28, 1), (33, 1), (40, 1), (43, 1)] }, { coefficient := 2, powers := [(19, 1), (22, 1), (28, 1), (40, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (28, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (39, 1), (40, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (39, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (40, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (11, 1), (19, 1), (25, 1), (28, 1), (33, 1), (40, 1), (43, 1), (50, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (19, 1), (28, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (23, 1), (28, 1), (40, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (19, 1), (22, 1), (28, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(11, 1), (19, 1), (23, 1), (28, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(11, 1), (19, 1), (25, 1), (28, 1), (33, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(11, 1), (19, 1), (26, 1), (28, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := -2, powers := [(11, 1), (19, 1), (27, 1), (28, 1), (40, 1), (43, 1)] }, { coefficient := -2, powers := [(11, 1), (19, 1), (27, 1), (28, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(11, 1), (19, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (24, 1), (54, 2), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (24, 1), (54, 1), (55, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (28, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(16, 1), (19, 1), (23, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := -2, powers := [(16, 1), (19, 1), (23, 1), (28, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (51, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (51, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (25, 1), (28, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (28, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB4_3_3.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB4_3_3
