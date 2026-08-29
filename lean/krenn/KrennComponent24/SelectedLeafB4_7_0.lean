import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB4_7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "70d2fce0f15dc18cc02d8b22b25e032647e6c16709cc623a84f96096f4d2886c"
def certificateSHA256 : String := "2bfb756041dfe919e62158c7d372d92894bc0e5ab6d4b1c525f9490f54554764"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 673 := ![
  2,
  15,
  23,
  50,
  128,
  132,
  153,
  160,
  164,
  176,
  196,
  259,
  307,
  316,
  321,
  323,
  417,
  452,
  457,
  471,
  504,
  585,
  597,
  598,
  612,
  663,
  666,
  667,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (43, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (49, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (43, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (43, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (43, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (43, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (43, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (42, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (26, 1), (43, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (41, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (49, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (25, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (31, 1), (43, 1), (49, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (31, 1), (41, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (43, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (43, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (43, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (42, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1), (43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (40, 1), (43, 1), (60, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(43, 1), (49, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (26, 1), (37, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (31, 1), (43, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (31, 1), (43, 1), (49, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (25, 1), (43, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (41, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 2), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (14, 1), (25, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (30, 1), (41, 1), (43, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB4_7_0.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB4_7_0
