import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB6_6_1_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "db3698b65386172fac94feefa8b783a4822c61d89671475a6dd70d36e8b0a1ac"
def certificateSHA256 : String := "1e77952ac6785ee138a768b4bd0493fff28f3624a4cc4076e5b82a7fc2ee6148"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 675 := ![
  2,
  10,
  18,
  20,
  22,
  170,
  267,
  302,
  304,
  318,
  324,
  403,
  412,
  420,
  424,
  429,
  446,
  452,
  565,
  608,
  610,
  662,
  663,
  665,
  668,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1)] }, { coefficient := 1, powers := [(46, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (39, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (35, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (27, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (25, 1), (27, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (39, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (30, 1), (43, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (39, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (21, 1), (43, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (39, 1), (43, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (21, 1), (43, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (32, 1), (39, 1), (43, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (21, 1), (32, 1), (43, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (39, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (39, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (25, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (32, 1), (43, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(43, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (32, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (21, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (43, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (25, 1), (39, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (21, 1), (25, 1), (43, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (43, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (43, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (25, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (21, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (32, 1), (39, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (21, 1), (32, 1), (43, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (41, 1), (43, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (43, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (41, 1), (43, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (43, 1), (50, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (39, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (38, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (32, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (21, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (21, 1), (38, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (21, 1), (32, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (21, 1), (25, 1), (39, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (21, 1), (32, 1), (39, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (21, 2), (25, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (21, 2), (32, 1), (43, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1)] }, { coefficient := -1, powers := [(21, 1), (43, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (32, 1), (39, 1), (43, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (39, 1), (43, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (25, 1), (39, 1), (43, 2), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (21, 1), (32, 1), (43, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (21, 1), (25, 1), (43, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 1), (21, 1), (25, 1), (43, 2), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(27, 1), (43, 1), (46, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := 2, powers := [(43, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(49, 1), (54, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB6_6_1_1.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB6_6_1_1
