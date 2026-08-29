import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_6_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "629215181fd68d385f0371b3e0a9462f21d3ebdfa8d1b675dab1f97fb4ad8e13"
def certificateSHA256 : String := "a109f0cd9f57c4e84615324515f3595dd152d6df859238a5afd14c842fbfd9b4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 673 := ![
  26,
  173,
  304,
  305,
  318,
  476,
  477,
  511,
  515,
  537,
  602,
  603,
  644,
  659,
  661,
  662,
  664,
  667,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(10, 1), (27, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 2)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (62, 1)] }, { coefficient := -1, powers := [(51, 1), (62, 1)] }, { coefficient := -1, powers := [(56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (39, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1)] }, { coefficient := -1, powers := [(25, 1), (51, 1)] }, { coefficient := -1, powers := [(25, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (28, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (44, 1), (51, 2)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (39, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (44, 2), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 2), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (56, 2), (62, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(43, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := 1, powers := [(50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (20, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (25, 1), (44, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (33, 1), (36, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (38, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (38, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (38, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (20, 1), (44, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (25, 1), (44, 2), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (51, 2)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (38, 1), (44, 2), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (38, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (38, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 2)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (39, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (38, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (38, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (38, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 2)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (25, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (20, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (25, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (39, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (51, 2)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (44, 2)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_6_6_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_6_6_3
