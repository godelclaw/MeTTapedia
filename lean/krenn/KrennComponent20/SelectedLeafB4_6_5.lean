import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e0bfe5a7f0a43bd67546d673028a2e41adde553e827a6f8115a7c74aff16211e"
def certificateSHA256 : String := "73639becb029cddff11a455c7769d71f3763711db5dd99b56375bc3f968a54fe"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 645 := ![
  133,
  163,
  179,
  185,
  186,
  189,
  190,
  191,
  197,
  284,
  291,
  315,
  317,
  352,
  362,
  462,
  466,
  480,
  506,
  558,
  628,
  635,
  638,
  641,
  642,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (49, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := -1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(21, 1), (44, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(36, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (20, 1), (24, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (24, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_6_5.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_6_5
