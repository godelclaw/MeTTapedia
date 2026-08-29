import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_6_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "eb06f350cd694b40a21816c2cd5ae35af98cfa856270001801579b794f4c57e5"
def certificateSHA256 : String := "0808514d81a0cdf7f67a179bffbd4f320036af8480a4543c00efd0d072dc5fd2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 673 := ![
  23,
  180,
  181,
  187,
  277,
  300,
  301,
  302,
  303,
  304,
  305,
  316,
  419,
  425,
  430,
  434,
  463,
  470,
  476,
  477,
  482,
  563,
  603,
  659,
  660,
  661,
  662,
  663,
  664,
  666,
  667,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (45, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (22, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (38, 1), (45, 1), (54, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (45, 1), (50, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (38, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (38, 1), (51, 1), (54, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (39, 1), (54, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (43, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (50, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (38, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (43, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (50, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (22, 1), (33, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (31, 1), (33, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (22, 1), (33, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (31, 1), (33, 1), (37, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (22, 1), (30, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (30, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (20, 1), (22, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (22, 1), (38, 1), (45, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (31, 1), (37, 1), (38, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (22, 1), (38, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (31, 1), (37, 1), (38, 1), (51, 1), (62, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_6_6_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_6_6_5
