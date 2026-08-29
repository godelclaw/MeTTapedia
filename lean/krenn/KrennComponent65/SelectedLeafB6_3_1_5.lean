import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB6_3_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "114eb1258d47c6b02884e03608c3a0eec5b577927d2fe9a29ddc0916cec5234f"
def certificateSHA256 : String := "42aad60e5727bc0ad4477c8f4c6035854eb3a9488e8276239891f85589c7cd82"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 674 := ![
  12,
  15,
  18,
  19,
  26,
  29,
  198,
  203,
  309,
  310,
  315,
  414,
  421,
  423,
  434,
  540,
  581,
  582,
  607,
  661,
  664,
  669,
  670,
  671,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (35, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (44, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (34, 1), (35, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (35, 1), (40, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (35, 1), (44, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (35, 1), (44, 1), (47, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (47, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (35, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (35, 1), (44, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (35, 1), (44, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (46, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (44, 2), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (44, 2), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 2), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (44, 2), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (37, 1), (44, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (40, 1), (44, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (44, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (47, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (44, 2), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (28, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (44, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (35, 1), (44, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (28, 1), (35, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (44, 2)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB6_3_1_5.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB6_3_1_5
