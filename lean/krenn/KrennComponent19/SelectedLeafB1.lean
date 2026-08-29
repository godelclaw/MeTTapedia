import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "00850c0bc66c8c918e204b73fcf7a49ded801fbbbe05864baabc815fca82a18b"
def certificateSHA256 : String := "8040e655318223bc757186c3f92f0cb7e03cfd10d7eab8ad44d1362d9ff4cc9a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 666 := ![
  2,
  9,
  18,
  20,
  22,
  191,
  198,
  200,
  203,
  304,
  318,
  402,
  420,
  424,
  428,
  429,
  439,
  440,
  449,
  463,
  468,
  489,
  513,
  565,
  582,
  583,
  610,
  662,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (43, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(32, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(35, 1), (39, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (39, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (39, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (39, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (31, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(31, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (32, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (31, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 2), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (31, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (31, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (44, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (48, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (39, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (39, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (39, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (32, 1), (39, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (31, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (39, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (31, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (39, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1), (39, 1), (44, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB1
