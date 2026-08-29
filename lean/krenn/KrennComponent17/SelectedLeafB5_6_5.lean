import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "075eb263a8b8731b70f16aaba58b206dcd39d8b8e7900bdc141a16dc43e74dee"
def certificateSHA256 : String := "da8304afafaff1ba820d671df13452249f0af67a12db47dfd3382ea8d4cc8437"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 611 := ![
  5,
  18,
  19,
  21,
  27,
  32,
  183,
  205,
  210,
  211,
  311,
  325,
  330,
  351,
  430,
  433,
  434,
  438,
  440,
  441,
  445,
  468,
  550,
  552,
  577,
  601,
  602,
  607,
  608,
  609
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(29, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (23, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (29, 1), (36, 1), (50, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (25, 1), (36, 1), (46, 1), (50, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (38, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (36, 1), (50, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(29, 1), (36, 1), (46, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (43, 1), (50, 2), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (43, 1), (50, 2)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (20, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (46, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (36, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (25, 1), (36, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (19, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (25, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (53, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (29, 1), (36, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (25, 1), (36, 1), (46, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (25, 1), (36, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1), (58, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (36, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (29, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (25, 1), (36, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (25, 1), (36, 1), (58, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_5.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_5
