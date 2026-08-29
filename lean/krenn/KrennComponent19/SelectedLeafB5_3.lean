import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ec2e946473f80309924f4a0845266d6ee64644e8dc26f974c42aeb36a8d56f60"
def certificateSHA256 : String := "a951c7f7fb95dd6fc43409af2ffe802864db3ae67434026d13af888c0b21ede3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 669 := ![
  0,
  2,
  3,
  10,
  17,
  18,
  20,
  22,
  23,
  27,
  28,
  170,
  187,
  191,
  203,
  267,
  304,
  318,
  320,
  403,
  419,
  420,
  424,
  429,
  463,
  565,
  582,
  583,
  608,
  655,
  662,
  663,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (39, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (41, 1), (61, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (41, 1), (61, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (35, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (25, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (30, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -2, powers := [(21, 1), (25, 1), (49, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (43, 1), (44, 1), (49, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (44, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (49, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(32, 1), (44, 1), (49, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (53, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (53, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (43, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (48, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (53, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (57, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (32, 1), (50, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (43, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (43, 2), (44, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (43, 1), (44, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (43, 1), (44, 1), (54, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (44, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (32, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1)] }, { coefficient := -2, powers := [(13, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 1), (43, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (21, 1), (25, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (41, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (30, 1), (41, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (24, 1), (35, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (30, 1), (35, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (25, 1), (30, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (25, 1), (26, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (25, 1), (26, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (25, 1), (26, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (25, 1), (26, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (25, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (32, 1), (43, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (32, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (44, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (44, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (26, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (32, 1), (43, 2), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (32, 1), (43, 1), (44, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (43, 1), (44, 1), (54, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_3.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_3
