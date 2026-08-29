import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "51731607498bd0358bc993672564df2b9ba75a872fb8686a45b57f11630db85f"
def certificateSHA256 : String := "e5843b935ae529228cc5e66cfa9d0032f93d005a595b6bbc8fcc1d58fe38aa87"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 673 := ![
  10,
  11,
  14,
  26,
  191,
  193,
  232,
  280,
  304,
  305,
  425,
  440,
  478,
  542,
  566,
  603,
  659,
  660,
  662,
  663,
  665,
  666,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(7, 1), (31, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (39, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (36, 1), (44, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (39, 1), (42, 1), (59, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (22, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (42, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (36, 1), (42, 1), (59, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (22, 1), (36, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (33, 1), (39, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (33, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (39, 1), (59, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (36, 1), (59, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (36, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := -1, powers := [(45, 1), (53, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (33, 1), (34, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (20, 1), (22, 1), (39, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (20, 1), (22, 1), (36, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (33, 1), (39, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (33, 1), (39, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (33, 1), (39, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (33, 1), (39, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (33, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (33, 1), (36, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (33, 1), (36, 1), (46, 1), (49, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_3_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_3_4
