import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "84f1d4d95dae56fa74256fb84bc089df3cb4644430991801683f25dd611d981f"
def certificateSHA256 : String := "d4a14fddfd78c73295e0ddb9a1eb42f36ebaf397bc24cf6cef3e9ee2a2679e9a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 608 := ![
  1,
  2,
  4,
  7,
  8,
  18,
  22,
  32,
  33,
  34,
  39,
  42,
  183,
  188,
  213,
  308,
  311,
  325,
  340,
  378,
  415,
  423,
  434,
  441,
  459,
  513,
  541,
  552,
  572,
  601,
  602,
  603,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (8, 1), (27, 1), (44, 1), (58, 1), (60, 2)] }],
  [{ coefficient := -2, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (8, 1), (23, 1), (44, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (21, 1), (23, 1), (58, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (25, 1), (41, 1), (45, 1), (50, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (45, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (41, 1), (45, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (45, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1), (45, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (15, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (16, 1), (34, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (23, 1), (34, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (23, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (8, 1), (44, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (25, 1), (41, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (25, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (34, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (8, 1), (27, 1), (44, 1), (46, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (25, 1), (41, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (41, 1), (43, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (25, 1), (41, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (41, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (25, 1), (41, 1), (45, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (41, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (15, 1), (21, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (25, 1), (41, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (41, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (29, 1), (41, 1), (45, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB7_5.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB7_5
