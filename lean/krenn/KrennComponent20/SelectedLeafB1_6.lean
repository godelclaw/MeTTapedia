import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "36e87bbf0205bd54a882b314153edb2b72cfcde7d5bb6e8ec41c2503eabf7f41"
def certificateSHA256 : String := "758da28e1c3a37c19a6cc9527cf759b3d2ef7ebb6ec898ff61dcf4c1208f8405"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 642 := ![
  15,
  23,
  179,
  187,
  188,
  189,
  190,
  191,
  193,
  194,
  197,
  198,
  347,
  350,
  351,
  353,
  360,
  369,
  440,
  462,
  465,
  466,
  473,
  479,
  480,
  484,
  494,
  506,
  551,
  592,
  621,
  635,
  636,
  638,
  639,
  640,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (21, 1), (43, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (25, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (29, 1), (47, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (36, 1), (46, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (25, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (26, 1), (32, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (24, 1), (26, 1), (43, 1), (49, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (24, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (36, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (43, 1), (49, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (43, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (36, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (25, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (36, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (43, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (43, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (40, 1), (49, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (43, 1), (45, 1), (49, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (43, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (37, 1), (47, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (40, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1), (47, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (36, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (37, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (40, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (45, 1), (51, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (50, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (43, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (43, 1), (45, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (47, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (45, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (43, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB1_6.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB1_6
