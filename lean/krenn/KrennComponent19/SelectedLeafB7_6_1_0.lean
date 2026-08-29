import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB7_6_1_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "531f8f0d5e745e9da38c73e39cede6b1fe45354c37d475ecc94947f94ef4a07e"
def certificateSHA256 : String := "12f24699b0541001b3514f3910778db642e736fb8289c79dc93b80ec2831bbfe"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 675 := ![
  2,
  9,
  10,
  18,
  20,
  22,
  170,
  267,
  318,
  402,
  403,
  420,
  424,
  429,
  463,
  464,
  565,
  662,
  663,
  665,
  668,
  670,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(32, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(35, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (39, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (35, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(30, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (38, 1), (39, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (24, 1), (35, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (24, 1), (35, 1), (48, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (30, 1), (35, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (30, 1), (35, 1), (48, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1), (48, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (39, 1), (41, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (35, 1), (39, 1), (41, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (50, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB7_6_1_0.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB7_6_1_0
