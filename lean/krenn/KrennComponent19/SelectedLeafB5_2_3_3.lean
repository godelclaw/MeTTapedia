import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_2_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "14e969c2bdb5c85bada72d41856945b217a0eff8a65996f3590723afe9b0b9a3"
def certificateSHA256 : String := "6222864278c72144cd8d8c4f5f8023cf7f0d2e5d216a1d260af1d4f08f696ef9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 675 := ![
  10,
  18,
  20,
  22,
  170,
  171,
  196,
  220,
  267,
  302,
  304,
  318,
  319,
  324,
  403,
  420,
  424,
  429,
  442,
  446,
  470,
  565,
  582,
  662,
  663,
  667,
  668,
  670,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1)] }, { coefficient := 1, powers := [(32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (58, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (55, 1), (62, 2)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (32, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (58, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (27, 1), (53, 2), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (53, 1), (54, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (58, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (27, 1), (53, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (53, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (58, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (48, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1), (46, 1), (53, 2), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (43, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (46, 1), (53, 1), (54, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (48, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (32, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (48, 1), (58, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_2_3_3.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_2_3_3
