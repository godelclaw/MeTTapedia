import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0fcd88429d4a9b0ecd07483fe2d7498e41ebd4d55740e4b2f48bbf124e412994"
def certificateSHA256 : String := "8c2b64d39408456bde309e61f8dcad1b491bd8706daf08ff3585925b166f5bce"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 639 := ![
  0,
  1,
  2,
  3,
  5,
  187,
  191,
  193,
  196,
  199,
  352,
  440,
  470,
  479,
  480,
  484,
  485,
  498,
  506,
  551,
  592,
  635,
  636,
  637,
  638
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (41, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (52, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (35, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (29, 1), (45, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (18, 1), (24, 1), (25, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (18, 1), (24, 1), (25, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (24, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (28, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (25, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (36, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (41, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (35, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (29, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (59, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB3
