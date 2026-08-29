import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_2_7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c16de7787b8e9f24649c263d759503461a71a5e2bd9bcd8046a52f43eaeecea1"
def certificateSHA256 : String := "6fce6904a306f006dd96d3908d1e1afc8340d2fd4cae4b57de75012a643ae99e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 670 := ![
  171,
  179,
  180,
  181,
  312,
  393,
  394,
  410,
  411,
  433,
  438,
  450,
  454,
  561,
  566,
  570,
  650,
  657,
  660,
  663,
  664,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (44, 1), (48, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (48, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1), (48, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := -2, powers := [(24, 1), (51, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (53, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := -2, powers := [(24, 1), (55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (51, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (48, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 2), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (45, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (41, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (41, 1), (48, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (46, 1), (48, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (47, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (41, 1), (44, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (41, 1), (51, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (41, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (46, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (45, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (46, 1), (51, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (46, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (47, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (41, 1), (55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (44, 1), (46, 1), (48, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (47, 1), (48, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1), (58, 1), (66, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_2_7_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_2_7_0
