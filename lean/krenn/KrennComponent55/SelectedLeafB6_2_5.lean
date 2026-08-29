import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB6_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fa0fc80200185f38305064cbbe5e23b2ea362f4650f66361d7100e78917a0dea"
def certificateSHA256 : String := "b3f608419e6bb865bf5debe62008f5807cff7611746b66451176423bee43280d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 593 := ![
  24,
  25,
  217,
  223,
  225,
  228,
  232,
  234,
  257,
  296,
  341,
  342,
  345,
  354,
  360,
  361,
  362,
  390,
  450,
  480,
  490,
  512,
  583,
  586,
  588,
  589,
  590,
  591
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(45, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (38, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(38, 1), (57, 1)] }, { coefficient := -2, powers := [(40, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (29, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (60, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB6_2_5.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB6_2_5
