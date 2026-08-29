import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e3edeefe89d705a5c1b54ba7560a4055f2d385538046700c29eebb95fe6383ad"
def certificateSHA256 : String := "402b5f418002015c81469f8012731ceb02ee5ea7e3e5f446bd19d27187f3bb5e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 668 := ![
  12,
  15,
  18,
  23,
  26,
  29,
  302,
  304,
  309,
  310,
  317,
  318,
  320,
  423,
  439,
  447,
  540,
  581,
  611,
  661,
  662,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (34, 1), (44, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (31, 1), (44, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (44, 1), (47, 1), (51, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (44, 2), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (44, 1), (53, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (44, 1), (46, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (44, 1), (51, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (23, 1), (44, 2), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (44, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (44, 1), (47, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(44, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (23, 1), (44, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (28, 1), (44, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (44, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (39, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (44, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(44, 2), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (44, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(44, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (44, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (39, 1), (44, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 2), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (46, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (44, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(44, 2), (62, 1)] }, { coefficient := -1, powers := [(44, 1), (46, 1), (52, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (37, 1), (44, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (40, 1), (44, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 3, powers := [(6, 1), (44, 1), (47, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(24, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 2), (62, 1)] }, { coefficient := -1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [(44, 1), (62, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB2_3.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB2_3
