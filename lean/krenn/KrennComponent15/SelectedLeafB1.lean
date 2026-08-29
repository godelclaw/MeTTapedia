import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c597946e52d1b3ae949d9ae5788a87dfd49b910f9e1c5d0b47b44e98c27ab72e"
def certificateSHA256 : String := "efc1e7746dc6da653a5dc41eda7ae0a538833c012e0174a6571b090a6f82e820"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 589 := ![
  7,
  9,
  13,
  17,
  210,
  222,
  224,
  231,
  234,
  245,
  315,
  336,
  359,
  360,
  365,
  367,
  376,
  381,
  429,
  475,
  495,
  527,
  585,
  586,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (37, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (32, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (38, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (23, 1), (38, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (29, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (29, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (29, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (22, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (23, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (29, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (33, 1), (56, 1)] }, { coefficient := -1, powers := [(32, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (43, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (23, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (29, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (48, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (43, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (42, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (38, 1), (40, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (38, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (29, 1), (40, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (29, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (29, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (33, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (32, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (22, 1), (40, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (23, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (29, 1), (35, 1), (48, 1)] }]
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
    (values : Fin 58 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB1
