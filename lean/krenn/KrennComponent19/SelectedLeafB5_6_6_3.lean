import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_6_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5f5a9cbc33d121e0df2a415d70845dc5dd5514a28aedd9aaa21ac075e5d20e44"
def certificateSHA256 : String := "ca451959df184d4ed0d902dd44e0d627223b7f16dda50b38321a31dd5db4b4c0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 675 := ![
  10,
  18,
  20,
  22,
  170,
  171,
  304,
  318,
  403,
  420,
  424,
  429,
  442,
  565,
  662,
  663,
  668,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (27, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (55, 1), (62, 2)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (32, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (55, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (25, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (32, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (32, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (50, 1), (55, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (32, 1), (50, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (25, 1), (43, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (55, 1), (62, 2)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_6_6_3.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_6_6_3
