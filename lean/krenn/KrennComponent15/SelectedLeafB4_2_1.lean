import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB4_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f8bd57bb4fe4106a997ae60acd5cb89c7302b573fd7978474c00135085f25375"
def certificateSHA256 : String := "74411bd5f99a137cd53ca2996a96158143137885755a46bd1dd7bd8dbf793f3e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 595 := ![
  13,
  17,
  222,
  228,
  229,
  232,
  234,
  315,
  339,
  359,
  365,
  366,
  367,
  368,
  376,
  466,
  471,
  475,
  481,
  485,
  527,
  528,
  547,
  585,
  588,
  590,
  591,
  593
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (33, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (33, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (29, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (29, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (40, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -4, powers := [(3, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(26, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (8, 1), (56, 1)] }, { coefficient := -4, powers := [(8, 1), (17, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 4, powers := [(21, 1), (53, 1)] }, { coefficient := 2, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (21, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(50, 1)] }],
  [{ coefficient := 2, powers := [(37, 1), (44, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(26, 1)] }],
  [{ coefficient := -2, powers := [(21, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (29, 1), (37, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (37, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (37, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (29, 1), (37, 1), (40, 1)] }, { coefficient := 4, powers := [(8, 1), (21, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(35, 1), (56, 1)] }, { coefficient := -2, powers := [(37, 1), (44, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (53, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (8, 1), (21, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (23, 1), (29, 1), (37, 1), (40, 1)] }, { coefficient := -4, powers := [(12, 1), (17, 1), (21, 1), (53, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (32, 1), (35, 1)] }, { coefficient := -2, powers := [(12, 1), (26, 1), (44, 1), (58, 1)] }, { coefficient := -2, powers := [(16, 1), (17, 1), (21, 1), (46, 1), (49, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB4_2_1.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB4_2_1
