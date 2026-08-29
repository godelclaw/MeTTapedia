import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "68aec4f089d06b7768c91b64bfab65369d5da253c7cc7e6daeb289f89da8902f"
def certificateSHA256 : String := "2033267922ea7959d88d82431762d7030a328a6d628355016ef3c05bcaf6c6fe"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 673 := ![
  2,
  15,
  17,
  18,
  19,
  23,
  128,
  153,
  161,
  167,
  307,
  323,
  417,
  451,
  452,
  457,
  461,
  462,
  471,
  503,
  504,
  571,
  657,
  663,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(25, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (53, 1), (54, 1), (58, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (29, 1), (54, 1), (57, 1), (58, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (54, 1), (58, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (38, 1), (53, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (38, 1), (57, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (54, 1), (57, 1), (58, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (54, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (67, 1)] }, { coefficient := -2, powers := [(26, 1), (31, 1), (49, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (48, 1), (61, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (46, 1), (49, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 2), (58, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := 2, powers := [(14, 1), (31, 1), (49, 1), (57, 1), (67, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (46, 1), (55, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (57, 1), (58, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (49, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(31, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (58, 1)] }, { coefficient := -2, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (25, 1), (57, 2), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (25, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (31, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (30, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (53, 1), (54, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (54, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (54, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (26, 1), (54, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (26, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (26, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1), (48, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (25, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (31, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_2_3.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_2_3
