import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c18c85c79ccc2b3c5ffc1b46feae7aed06e7f38128fef6c24f6712d2a6a97978"
def certificateSHA256 : String := "c37324f390a52a77ee7cf2214c6a5b174e84cf439aaba6fbb86adbdc4dd805d5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 614 := ![
  30,
  32,
  40,
  41,
  43,
  209,
  211,
  300,
  308,
  309,
  325,
  434,
  446,
  541,
  542,
  555,
  556,
  570,
  600,
  601,
  602,
  603,
  605,
  607,
  610,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := -1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(7, 1), (43, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (44, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (34, 1), (44, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (34, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (34, 1), (37, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (34, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (11, 1), (34, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (34, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (23, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (23, 1), (34, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (13, 1), (34, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (34, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (18, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(15, 1), (34, 1), (37, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (13, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (11, 1), (34, 1), (37, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (34, 1), (37, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (23, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (23, 1), (34, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (57, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(40, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(40, 1), (54, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(40, 1), (54, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (11, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (34, 1), (35, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := -1, powers := [(10, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (39, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (34, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (34, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (34, 1), (37, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_3_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_3_4
