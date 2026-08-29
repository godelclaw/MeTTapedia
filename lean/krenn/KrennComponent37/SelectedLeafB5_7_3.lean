import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7d4f4696ae77257fd599e6b3472e21b349d13fe447a28dd175dbb1201371feb3"
def certificateSHA256 : String := "9dc4d5a040b5cde66af51500d6a8abcf33ef71d2055bae294f97e17ed1cd875f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 667 := ![
  23,
  27,
  48,
  147,
  152,
  182,
  283,
  298,
  299,
  303,
  354,
  373,
  583,
  584,
  589,
  590,
  604,
  605,
  656,
  659,
  661,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (44, 1), (57, 1), (60, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (44, 1), (46, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := 2, powers := [(9, 1), (15, 1), (44, 1), (46, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (44, 1), (52, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := 2, powers := [(9, 1), (15, 1), (44, 1), (57, 2), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (16, 1), (46, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (44, 1), (46, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (51, 1), (57, 1), (60, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -2, powers := [(9, 1), (10, 1), (46, 1), (51, 1), (57, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (51, 1), (57, 2), (64, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (11, 1), (41, 1), (57, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -2, powers := [(9, 1), (15, 1), (41, 1), (51, 1), (57, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (51, 1), (52, 1), (57, 1), (64, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (52, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (41, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (57, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (57, 1), (60, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := 2, powers := [(9, 1), (10, 1), (46, 1), (57, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (57, 2), (64, 1), (66, 1), (67, 1)] }, { coefficient := 2, powers := [(9, 1), (15, 1), (41, 1), (57, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (52, 1), (57, 1), (64, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (57, 1), (60, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (46, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -2, powers := [(9, 1), (15, 1), (46, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (52, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -2, powers := [(9, 1), (15, 1), (57, 2), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (46, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (52, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (46, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := 2, powers := [(15, 1), (22, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (41, 1), (57, 1), (64, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (27, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (38, 1), (57, 1), (60, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (42, 1), (57, 2), (64, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (41, 1), (46, 1), (57, 1), (58, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (48, 1), (53, 1), (57, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (41, 1), (57, 2), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (46, 1), (47, 1), (54, 1), (57, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (46, 1), (52, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (46, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (27, 1), (57, 1), (60, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (35, 1), (41, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := -2, powers := [(9, 1), (10, 1), (27, 1), (46, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (27, 1), (57, 2), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (27, 1), (41, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (27, 1), (52, 1), (57, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (32, 1), (46, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (31, 1), (52, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (31, 1), (41, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (31, 1), (46, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (22, 1), (57, 1), (60, 1), (64, 1), (67, 1)] }, { coefficient := 2, powers := [(9, 1), (15, 1), (22, 1), (46, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (22, 1), (52, 1), (57, 1), (64, 1), (67, 1)] }, { coefficient := 2, powers := [(9, 1), (15, 1), (22, 1), (57, 2), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (40, 1), (46, 1), (57, 1), (64, 1), (67, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_7_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_7_3
