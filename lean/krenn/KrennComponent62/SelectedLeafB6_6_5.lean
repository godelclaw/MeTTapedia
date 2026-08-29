import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB6_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ef52b046418f66370b0703d8bb3a4d495f3bf5c9dca4d5887652972ecd636dc5"
def certificateSHA256 : String := "90d0deec00d04620f2b77e4703cc054b609d9f237a16cb66dcf123119c71259f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 667 := ![
  18,
  21,
  135,
  137,
  151,
  153,
  158,
  186,
  223,
  301,
  302,
  309,
  311,
  337,
  390,
  408,
  454,
  557,
  579,
  598,
  619,
  657,
  660,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (45, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (45, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(46, 1), (48, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (22, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (51, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (53, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (22, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (23, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1), (46, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (23, 1), (53, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (53, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (56, 1), (58, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (45, 1), (52, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (45, 1), (48, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(39, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 2), (65, 1)] }, { coefficient := -1, powers := [(45, 1), (48, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1), (52, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (18, 1), (22, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (22, 1), (23, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (27, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (27, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (53, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB6_6_5.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB6_6_5
