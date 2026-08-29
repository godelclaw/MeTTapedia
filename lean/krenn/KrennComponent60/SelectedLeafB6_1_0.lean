import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_1_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fef6b2e6b62e5837744c7a37827a0cdbfe0b2c706bc80a56de1251b138497130"
def certificateSHA256 : String := "e342ce0d533229859333a55b110995ac1e2fcff5a170cfb2c5a4898e810eb529"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 665 := ![
  13,
  22,
  25,
  172,
  173,
  292,
  298,
  301,
  303,
  310,
  314,
  404,
  422,
  423,
  443,
  458,
  462,
  466,
  517,
  556,
  578,
  582,
  587,
  600,
  601,
  612,
  653,
  655,
  656,
  657,
  658,
  659,
  660,
  661,
  662,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 2), (14, 1), (22, 2), (45, 1), (62, 2)] }, { coefficient := -2, powers := [(0, 2), (22, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (20, 1), (22, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (22, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (22, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (25, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (43, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (46, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (14, 1), (22, 1), (45, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 2), (42, 1), (45, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (20, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (45, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (42, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (43, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (14, 1), (22, 1), (45, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 2), (42, 1), (45, 1), (49, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (20, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (41, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (1, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (14, 1), (15, 1), (22, 1), (27, 1), (45, 1), (62, 2)] }, { coefficient := 1, powers := [(0, 2), (14, 1), (27, 1), (45, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 2), (15, 1), (27, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (25, 1), (42, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (33, 1), (36, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 2), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (33, 1), (45, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (15, 1), (20, 1), (27, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (15, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (20, 1), (27, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (25, 1), (27, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (27, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (29, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (25, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (45, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (25, 1), (30, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (33, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (20, 1), (25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (20, 1), (33, 1), (36, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (59, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_1_0.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_1_0
