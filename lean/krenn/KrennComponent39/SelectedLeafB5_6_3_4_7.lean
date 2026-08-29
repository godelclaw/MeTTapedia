import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_3_4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b2561d3a21e03e0a3b7d37fe6a8d3a7728d5209c0502347e1566688e3719d766"
def certificateSHA256 : String := "2883d2e7bf111442e50f308f1f529774a9f46631cadd8d292f570e4f1d979553"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 676 := ![
  14,
  19,
  26,
  171,
  184,
  190,
  195,
  232,
  280,
  304,
  305,
  343,
  347,
  444,
  603,
  659,
  661,
  662,
  663,
  669,
  671,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (45, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (42, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (42, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (39, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (56, 1), (70, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (21, 1), (33, 1), (61, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (33, 1), (61, 1), (62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (14, 1), (33, 1), (61, 1), (62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (17, 1), (33, 1), (61, 1), (62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(39, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (33, 1), (61, 1), (62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (33, 1), (61, 1), (62, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (33, 1), (61, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (44, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (33, 1), (42, 1), (52, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (45, 1), (49, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_3_4_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_3_4_7
