import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e1e29e65269c5c50df6caea9b9c57208eee0436bf449645788549c32c43f67ee"
def certificateSHA256 : String := "8ab0795bbfcc27191d6a14ac5342dff02b6a191f3556055dcb121e121351442b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 642 := ![
  0,
  1,
  2,
  3,
  4,
  5,
  163,
  188,
  189,
  191,
  328,
  352,
  387,
  400,
  415,
  470,
  480,
  498,
  551,
  558,
  592,
  635,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (26, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (18, 1), (29, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (29, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (29, 1), (55, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (29, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (43, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (23, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (46, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (46, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (6, 1), (18, 1), (29, 1), (46, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (23, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (29, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (29, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (41, 1)] }]
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

#print axioms Krenn.Component20.SelectedLeafB6_7.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB6_7
