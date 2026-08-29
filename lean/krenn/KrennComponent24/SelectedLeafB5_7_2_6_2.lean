import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_7_2_6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f1c219305d5c0524689630ba32a7392b6a9e66c6d7fd3649df62b28e680c6a92"
def certificateSHA256 : String := "2592d5a145673c10da95bc42d92c84f9ba52755a69928e21f2607b29af7fb7af"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 679 := ![
  2,
  14,
  15,
  131,
  149,
  159,
  266,
  305,
  306,
  323,
  457,
  471,
  606,
  607,
  635,
  661,
  663,
  666,
  669,
  670,
  672,
  675,
  676,
  677,
  678
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (35, 1), (37, 1), (43, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (37, 1), (43, 1), (50, 1), (70, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (37, 1), (41, 1), (43, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (32, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (24, 1), (35, 1), (49, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (35, 1), (41, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (37, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (35, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (32, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (26, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (14, 1), (35, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (19, 1), (35, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(9, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (35, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (35, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (15, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (20, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (18, 1), (24, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (21, 1), (37, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (32, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (32, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (21, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (26, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (35, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (35, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (24, 1), (35, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (14, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (19, 1), (35, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (35, 1), (48, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (35, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (35, 1), (41, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (9, 1), (35, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (37, 1), (41, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (35, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (9, 1), (25, 1), (35, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (25, 1), (35, 1), (41, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_7_2_6_2.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_7_2_6_2
