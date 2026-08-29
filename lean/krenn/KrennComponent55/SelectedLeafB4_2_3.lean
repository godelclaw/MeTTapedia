import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB4_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a574ea57741cf1798644dab7b29f97e638f541af5c9a56f58e5a7669b8267825"
def certificateSHA256 : String := "d5974fdb0276fa2fa32203a30b8fc150af5edc90acaf23b6f133b7bf7cc18900"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 593 := ![
  24,
  31,
  191,
  194,
  216,
  227,
  228,
  244,
  257,
  330,
  341,
  342,
  345,
  361,
  362,
  480,
  481,
  490,
  513,
  526,
  583,
  586,
  589,
  591
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 62) := ![
  [{ coefficient := 2, powers := [(3, 1), (50, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(36, 1), (50, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(50, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (18, 1), (32, 1), (54, 1)] }, { coefficient := -2, powers := [(18, 1), (32, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -2, powers := [(36, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (32, 1), (54, 1)] }, { coefficient := 2, powers := [(32, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (13, 1), (56, 1)] }, { coefficient := 2, powers := [(13, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(36, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(54, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(36, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(38, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (53, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (53, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (36, 1), (53, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (8, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (29, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (24, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (54, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB4_2_3.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB4_2_3
