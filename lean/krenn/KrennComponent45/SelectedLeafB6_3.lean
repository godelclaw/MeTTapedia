import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component45.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5b3423dee39e5e548625072798b30278a72621bef39c5f4f1f8502d9b5f61900"
def certificateSHA256 : String := "f12098ac6312306fe99714655a68331b464b91c8ef5ec5a792c17be69557792f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 566 := ![
  2,
  4,
  34,
  40,
  48,
  201,
  208,
  231,
  237,
  240,
  241,
  244,
  267,
  284,
  360,
  364,
  378,
  379,
  380,
  468,
  484,
  492,
  517,
  531,
  559,
  560,
  562,
  564,
  565
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (42, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (24, 1), (42, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (42, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (42, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (42, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (42, 1), (53, 1), (55, 1), (57, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (42, 1), (53, 1), (57, 1), (60, 2)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (42, 1), (46, 1), (57, 1), (60, 2)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (42, 1), (49, 1), (53, 1), (60, 2)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1), (48, 2), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (42, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (42, 1), (49, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (33, 1), (37, 1), (42, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (42, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (42, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (42, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (30, 1), (42, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (42, 1), (53, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (42, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (42, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (42, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(42, 2), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(42, 1), (48, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (42, 1), (53, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (42, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (42, 1), (46, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (42, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (30, 1), (42, 1), (48, 2), (59, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component45.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component45.SelectedLeafB6_3
