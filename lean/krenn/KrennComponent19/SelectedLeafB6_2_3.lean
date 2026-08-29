import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB6_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d4acdb90019d50d301a400dd9cf9306a129a2250fdc52d78de715b240e47ae8a"
def certificateSHA256 : String := "dc44da6dffc7ecbee0926f3b54a4dc69a6b8be433ae1c0ad8a8af083b5dc4d88"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 672 := ![
  2,
  5,
  7,
  10,
  14,
  18,
  20,
  22,
  172,
  173,
  187,
  196,
  220,
  304,
  318,
  420,
  424,
  429,
  470,
  565,
  582,
  583,
  662,
  664,
  665,
  668,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := -2, powers := [(3, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (28, 1), (32, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(25, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (22, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (32, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(21, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(21, 1), (58, 1)] }, { coefficient := -1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (53, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (31, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (53, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (31, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (21, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB6_2_3.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB6_2_3
