import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "143ce0f5e406403ce44c991031786f5d2766758a3c809eac0b4554ffb1c807fa"
def certificateSHA256 : String := "996a54838b142ea828bda42f65e465d0352cb231caed4eba46bb112bc74f1de7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 670 := ![
  5,
  14,
  23,
  168,
  171,
  175,
  179,
  181,
  185,
  256,
  279,
  280,
  294,
  295,
  296,
  297,
  298,
  299,
  307,
  310,
  311,
  316,
  393,
  438,
  445,
  446,
  450,
  454,
  476,
  482,
  485,
  510,
  562,
  567,
  604,
  605,
  656,
  657,
  658,
  659,
  663,
  665,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (15, 1), (29, 1), (39, 1), (61, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (46, 1)] }, { coefficient := -2, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (39, 1), (61, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (30, 1), (39, 1), (61, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (15, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (29, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (32, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (22, 1), (30, 1), (39, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (22, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (22, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (21, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (24, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (39, 1), (41, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (15, 1), (39, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (39, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (22, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (22, 1), (39, 1), (52, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_4_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_4_5
