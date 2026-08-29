import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_2_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c3b1c88818e509cbe7cd4f28bf543bbbf6e29f2c597dfdb5235dfac111ab62dd"
def certificateSHA256 : String := "83d7e9ab1cb97a1745f049c2991cfccd54f0ff465036ba5dc5cda9e8be3b61da"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 614 := ![
  7,
  60,
  77,
  190,
  210,
  306,
  307,
  311,
  312,
  325,
  327,
  330,
  334,
  415,
  430,
  454,
  541,
  549,
  550,
  567,
  568,
  571,
  599,
  601,
  602,
  604,
  605,
  607,
  608,
  609,
  610,
  611
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 64) := ![
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (23, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (19, 1), (23, 1), (33, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (23, 1), (30, 1)] }, { coefficient := 2, powers := [(8, 1), (19, 1), (23, 1), (33, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (19, 1), (23, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (36, 1), (55, 1), (57, 2), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (55, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (51, 1)] }],
  [{ coefficient := -4, powers := [(5, 1), (25, 1), (32, 1), (36, 1), (50, 2), (55, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (32, 1), (36, 1), (50, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (32, 1), (50, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 4, powers := [(5, 1), (32, 1), (36, 1), (50, 1), (51, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (36, 1), (51, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (51, 1), (54, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (32, 1), (50, 1)] }, { coefficient := -2, powers := [(13, 1), (27, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (50, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(29, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (8, 1), (23, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (19, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(18, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (33, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 4, powers := [(5, 1), (25, 1), (32, 1), (36, 1), (50, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (36, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (54, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (32, 1)] }, { coefficient := 2, powers := [(13, 1), (27, 1), (51, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(52, 1)] }],
  [{ coefficient := -4, powers := [(5, 1), (32, 1), (36, 1), (50, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (36, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (54, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (23, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (14, 1), (23, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (33, 1), (36, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (8, 1), (23, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1)] }, { coefficient := -2, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (9, 1), (23, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (23, 1), (39, 1), (58, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (23, 1), (30, 1), (58, 1)] }, { coefficient := 4, powers := [(8, 1), (9, 1), (19, 1), (23, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (19, 1), (23, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (32, 1), (36, 1), (55, 1), (57, 2)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (32, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 4, powers := [(5, 1), (19, 1), (32, 1), (36, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (36, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (32, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (9, 1), (23, 1), (33, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (23, 1), (33, 1), (48, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (40, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := 4, powers := [(5, 1), (25, 1), (32, 1), (36, 1), (43, 1), (50, 2), (55, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (36, 1), (43, 1), (50, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (43, 1), (50, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := -4, powers := [(5, 1), (32, 1), (36, 1), (43, 1), (50, 1), (51, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (36, 1), (43, 1), (51, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (43, 1), (51, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (14, 1), (23, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (23, 1), (42, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (42, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(13, 1), (27, 1), (47, 1), (50, 1), (51, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (45, 1), (52, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (40, 1), (52, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_2_3_1.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_2_3_1
