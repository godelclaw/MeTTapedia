import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_1_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6e82cf646e4c1ff258ca567da7679d5e7ff2c0f2ef60994923e7f9f99f1fa390"
def certificateSHA256 : String := "5f331ee5f6ba23ffd1dd8d7c33379e041b6077194236e2ca2b938775f47dacb6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 668 := ![
  22,
  27,
  147,
  293,
  301,
  302,
  316,
  404,
  410,
  422,
  443,
  444,
  446,
  455,
  456,
  463,
  517,
  556,
  557,
  585,
  645,
  650,
  655,
  656,
  658,
  660,
  661,
  662,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (33, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (33, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (50, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (48, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (51, 2), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (51, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (48, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (33, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (33, 1), (51, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (50, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (52, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(50, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(52, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (50, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (33, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (50, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (37, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (48, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (38, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (41, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (48, 1), (51, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (51, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (33, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (43, 1), (50, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (50, 1), (51, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (52, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (33, 1), (50, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (33, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (50, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (33, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (40, 1), (43, 1), (50, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (40, 1), (43, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (46, 1), (50, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (46, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (33, 1), (37, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (33, 1), (37, 1), (40, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (33, 1), (46, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (33, 1), (40, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (48, 1), (51, 2), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (40, 1), (50, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (40, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (33, 1), (37, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (33, 1), (37, 1), (47, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (33, 1), (48, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (33, 1), (47, 1), (50, 1), (51, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_1_6_0.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_1_6_0
