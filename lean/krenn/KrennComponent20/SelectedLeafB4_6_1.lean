import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "df529b107d592f4b7cb63e455db4b2e33734235ca2495951f619424b5667eb8d"
def certificateSHA256 : String := "7d70c1be4b82807fd2d2d62d45786e511a1fdf60424b71a5773f6e8f3ef370b9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 645 := ![
  34,
  144,
  163,
  184,
  186,
  188,
  189,
  190,
  196,
  198,
  199,
  284,
  317,
  320,
  344,
  347,
  352,
  353,
  367,
  458,
  462,
  466,
  480,
  484,
  490,
  558,
  598,
  621,
  635,
  638,
  640,
  641,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (45, 1), (49, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (49, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := -4, powers := [(24, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (20, 1), (53, 1)] }, { coefficient := 4, powers := [(19, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (26, 1), (32, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (32, 1), (45, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (26, 1), (32, 1), (40, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (35, 1)] }],
  [{ coefficient := -2, powers := [(29, 1), (47, 1)] }, { coefficient := 2, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (35, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(18, 1), (29, 1), (47, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (32, 1), (40, 1), (45, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (32, 1), (40, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (32, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (40, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (45, 1), (51, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (32, 1), (40, 1), (51, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(29, 1)] }],
  [{ coefficient := 2, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (40, 1), (43, 1), (45, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (40, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(53, 1)] }],
  [{ coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (32, 1), (40, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (32, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(38, 1), (59, 1)] }, { coefficient := 2, powers := [(41, 1), (56, 1)] }, { coefficient := -2, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (43, 1), (45, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := 4, powers := [(19, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (35, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (32, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (26, 1), (32, 1), (40, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (26, 1), (35, 1), (45, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (29, 1), (43, 1), (45, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (26, 1), (32, 1), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (26, 1), (35, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (29, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (35, 1), (49, 1)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (29, 1), (47, 1)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (35, 1), (38, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (29, 1), (47, 1), (49, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (29, 1), (46, 1), (49, 1)] }, { coefficient := -4, powers := [(19, 1), (24, 1), (53, 1), (62, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_6_1.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_6_1
