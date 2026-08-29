import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_2_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cb2bb5ad88bc34dea2a4bb8f92b372906f3e35a12a8d09dd15304f2392e8cf78"
def certificateSHA256 : String := "68c17cd79e0393174f64c305ebe927e8eedcdb7c1900873544f898baa9614a06"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 670 := ![
  9,
  15,
  26,
  27,
  28,
  130,
  180,
  181,
  269,
  295,
  309,
  311,
  433,
  445,
  449,
  450,
  453,
  454,
  478,
  487,
  516,
  619,
  657,
  658,
  663,
  664,
  665,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (41, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (46, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (41, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (46, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (54, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 1), (48, 1), (61, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (54, 1), (61, 1), (67, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (29, 1), (55, 1), (64, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (30, 1), (51, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (51, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (28, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (55, 1), (64, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (55, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (19, 1), (55, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (51, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (19, 1), (24, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (44, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (29, 1), (48, 1), (55, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (28, 1), (45, 1), (55, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (29, 1), (45, 1), (55, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (30, 1), (48, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_2_6_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_2_6_7
