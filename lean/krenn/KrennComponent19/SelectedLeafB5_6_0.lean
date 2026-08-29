import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e45febbbf26fc201e7de3a47f0ae3beb745f89bca44a4c4945e42868f4b459b4"
def certificateSHA256 : String := "20af50ef672160a9f128ffc6aca00b378985a35dbe788183345462d5164feb25"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 672 := ![
  2,
  10,
  18,
  20,
  22,
  171,
  196,
  267,
  304,
  316,
  318,
  403,
  420,
  424,
  429,
  442,
  565,
  583,
  662,
  663,
  665,
  668,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(3, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (27, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (30, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (38, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (20, 1), (26, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(20, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (32, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (32, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (25, 1), (26, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (25, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 2), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (32, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (13, 1), (21, 1), (32, 1), (50, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (25, 1), (26, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (21, 1), (38, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (25, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_6_0.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_6_0
