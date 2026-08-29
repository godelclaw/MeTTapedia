import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB6_1_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e751239afbb11f9bd1781ff0cdbf1b52a38ccd73ddab3d1ac4d4f9e0a266ff5d"
def certificateSHA256 : String := "882c37d7feea23abe798b24018e3cc34b5df6a95493fbfa8c97bdcefa234e27f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 673 := ![
  5,
  13,
  15,
  23,
  129,
  131,
  302,
  306,
  307,
  330,
  369,
  442,
  457,
  471,
  486,
  584,
  589,
  593,
  606,
  607,
  661,
  663,
  665,
  666,
  667,
  668,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(11, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (27, 2), (63, 2)] }, { coefficient := 2, powers := [(0, 1), (27, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (27, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(27, 1), (32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (22, 1), (25, 1), (35, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (22, 1), (25, 1), (35, 1), (38, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (35, 1), (38, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (38, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (25, 1), (35, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (35, 1), (38, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (27, 1), (63, 2)] }, { coefficient := -2, powers := [(0, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (51, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (51, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (27, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (40, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (26, 1), (51, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (26, 1), (50, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (41, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (11, 1), (22, 1), (27, 1), (63, 2)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (22, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (11, 1), (22, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (21, 1), (31, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (22, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (26, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (35, 1), (38, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB6_1_2.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB6_1_2
