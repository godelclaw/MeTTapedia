import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB6_7_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "84e64e8c3330ca1eec6c1876d62bf08710a6f1c6a213a326914f885d7ca4ae21"
def certificateSHA256 : String := "1acc11d4fdc5bcea9ff62225dad23207b95838ac28504475f4969bf3497b1b6c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 676 := ![
  1,
  13,
  15,
  22,
  23,
  129,
  131,
  132,
  149,
  151,
  160,
  161,
  190,
  266,
  306,
  307,
  323,
  369,
  452,
  457,
  471,
  590,
  593,
  606,
  607,
  661,
  663,
  665,
  666,
  669,
  670,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 71) := ![
  [{ coefficient := 2, powers := [(3, 1), (25, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (19, 1), (22, 1), (25, 1), (35, 1), (38, 1), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (22, 1), (25, 1), (35, 1), (38, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (50, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (27, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (50, 1), (70, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (70, 1)] }, { coefficient := -1, powers := [(26, 1), (41, 1), (70, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (70, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (26, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (35, 1), (38, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (38, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (19, 1), (25, 1), (35, 1), (38, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (35, 1), (38, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (31, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (37, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (70, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (26, 1), (55, 1), (59, 1), (70, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (25, 1), (35, 1), (38, 1), (55, 1), (70, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (35, 1), (38, 1), (50, 1), (55, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (26, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (31, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (40, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (40, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (35, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (41, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (22, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (26, 1), (31, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (21, 1), (31, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (21, 1), (37, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (37, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (50, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (32, 1), (38, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (26, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (25, 1), (26, 1), (55, 1), (59, 1), (70, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (35, 1), (38, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (25, 1), (35, 1), (38, 1), (55, 1), (70, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (35, 1), (38, 1), (50, 1), (55, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (44, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (27, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (26, 1), (45, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (35, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (26, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (25, 1), (35, 1), (38, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (35, 1), (38, 1), (45, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (44, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB6_7_2_7.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB6_7_2_7
