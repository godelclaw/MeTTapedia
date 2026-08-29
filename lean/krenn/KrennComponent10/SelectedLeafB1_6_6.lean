import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB1_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "da4b88eea1308fb91fca7ac2d01975b41053bcb7f287797615599b6059081da3"
def certificateSHA256 : String := "1ea156105d08c120a58633b38aadb03c534599e9fbf61aba635c7e46f5eb9565"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 644 := ![
  19,
  21,
  167,
  169,
  184,
  196,
  197,
  202,
  349,
  350,
  359,
  445,
  463,
  466,
  471,
  490,
  499,
  556,
  557,
  595,
  634,
  635,
  637,
  640,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(27, 1), (36, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (36, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (35, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (35, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(27, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (12, 1), (35, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (60, 1)] }, { coefficient := -1, powers := [(27, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (27, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (35, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (35, 1), (36, 1), (45, 1), (47, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (45, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (45, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (36, 1), (48, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (36, 1), (45, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (35, 1), (36, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(36, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (58, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB1_6_6.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB1_6_6
