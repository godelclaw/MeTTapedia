import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component54.SelectedLeafB0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "03cbff69f8ad54e8012c2804709837d196a0f85350f0c97766d11ba8825eae58"
def certificateSHA256 : String := "dc9e00457ecbb9e62fc86b611465fb9c8b17ee0abef4dc1db5e809b913f3496c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 642 := ![
  9,
  11,
  16,
  17,
  21,
  22,
  33,
  35,
  165,
  166,
  167,
  196,
  198,
  203,
  223,
  288,
  350,
  351,
  352,
  359,
  360,
  364,
  398,
  439,
  468,
  474,
  531,
  545,
  561,
  580,
  581,
  624,
  636,
  638,
  639,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (33, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 2), (57, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (36, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (30, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (33, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 2), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 2), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (25, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (33, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 2), (42, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (40, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (45, 1), (48, 1), (49, 1)] }, { coefficient := -2, powers := [(30, 1), (40, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(30, 1), (40, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (43, 1), (48, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (33, 1), (37, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(30, 1), (40, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(30, 1), (48, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (33, 1), (37, 1), (45, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (21, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (36, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (36, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(21, 1), (43, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(26, 1), (40, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (48, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (33, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (20, 1), (36, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (33, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (14, 1), (36, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (33, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(30, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (33, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (36, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (33, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (33, 1), (41, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (33, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (36, 1), (42, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (36, 1), (42, 1), (56, 2)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (43, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (39, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (42, 1), (57, 2), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (48, 1), (54, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (39, 1), (42, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (42, 2), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (42, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (26, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (40, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (48, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(26, 1), (40, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (48, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (40, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (48, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component54.SelectedLeafB0.selectedHasNoCommonZero

end Krenn.Component54.SelectedLeafB0
