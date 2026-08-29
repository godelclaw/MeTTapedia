import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component50.SelectedLeafB6_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d987d1f855fef118bd24a14250a1c08b871c0fed6b8aa3f9a987c8eb69fea554"
def certificateSHA256 : String := "a6701c56fbc79baa6852f4a9a25eacc951546f2610641720542d68b9810215cf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 644 := ![
  16,
  26,
  163,
  164,
  191,
  349,
  362,
  363,
  389,
  462,
  465,
  634,
  635,
  637,
  640,
  641,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 65) := ![
  [{ coefficient := -2, powers := [(24, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(30, 1), (47, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 2, powers := [(14, 1), (30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (21, 1), (30, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (26, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (53, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component50.SelectedLeafB6_4_5.selectedHasNoCommonZero

end Krenn.Component50.SelectedLeafB6_4_5
