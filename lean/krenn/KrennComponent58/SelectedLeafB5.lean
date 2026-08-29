import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d4760abf3436dbd8a0a44c09008ba257016cfdbf664cd621fe4c94704484f851"
def certificateSHA256 : String := "a1c4f6a3c5ae7a746e79ca639e0d7836d749cef325ea067e3dca515615ad70ac"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 616 := ![
  1,
  4,
  5,
  6,
  7,
  10,
  12,
  14,
  31,
  33,
  38,
  39,
  41,
  44,
  192,
  227,
  228,
  233,
  241,
  253,
  334,
  339,
  353,
  362,
  366,
  399,
  465,
  474,
  507,
  518,
  565,
  580,
  581,
  611,
  612,
  613,
  614,
  615
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (25, 1), (46, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (27, 1), (31, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (31, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (28, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (31, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (27, 1), (28, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (55, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(34, 1), (35, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (28, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (43, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (25, 1), (43, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (27, 1), (31, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (28, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (31, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (27, 1), (28, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (31, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (35, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (43, 1), (52, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB5
