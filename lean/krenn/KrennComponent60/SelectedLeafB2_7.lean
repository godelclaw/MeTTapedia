import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "eb1903f1d51f12b492eadf6234a90c084ddad4b2a3109ce63d8247b763dfb135"
def certificateSHA256 : String := "950088968f47a12a466c865f1b76c56205c1a503c55ebdfb96b00b563af57296"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 662 := ![
  18,
  20,
  22,
  25,
  149,
  168,
  292,
  294,
  301,
  302,
  312,
  314,
  359,
  424,
  434,
  436,
  443,
  458,
  459,
  463,
  466,
  467,
  556,
  601,
  608,
  609,
  655,
  656,
  658,
  659,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(18, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(26, 1), (32, 1), (36, 1), (45, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (35, 1), (36, 1), (41, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (30, 1), (36, 1), (45, 1), (52, 1), (62, 2)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (30, 1), (36, 1), (45, 1), (52, 1), (62, 2)] }, { coefficient := -2, powers := [(24, 1), (30, 1), (36, 1), (45, 1), (54, 1), (62, 2)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (41, 1), (45, 1), (62, 2)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (36, 1), (38, 1), (45, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (36, 1), (45, 1), (51, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (30, 1), (36, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (36, 1), (45, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (36, 1), (45, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (45, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (41, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (30, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (30, 1), (36, 1), (45, 1), (51, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1), (49, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (49, 1), (56, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (36, 1), (45, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (36, 1), (45, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (30, 1), (36, 1), (45, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1), (49, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(39, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (45, 1), (49, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (30, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (30, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (45, 1), (49, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (39, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (30, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (45, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(45, 1), (49, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (45, 1), (49, 1), (50, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (49, 1), (50, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (30, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (45, 1), (49, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (49, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(49, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (30, 1), (36, 1), (45, 1), (46, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (30, 1), (36, 1), (40, 1), (45, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (30, 1), (36, 1), (45, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (45, 1), (49, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (47, 1), (49, 1), (50, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (45, 1), (47, 1), (49, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (45, 2), (49, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (39, 1), (45, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (45, 2), (49, 1), (50, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (45, 1), (49, 1), (50, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (45, 1), (49, 1), (50, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (41, 1), (45, 1), (49, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (47, 1), (49, 1), (50, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (47, 1), (49, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(39, 1), (47, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (49, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1), (52, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (36, 1), (38, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (41, 1), (45, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (45, 1), (48, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (29, 1), (30, 1), (36, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (30, 1), (36, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (30, 1), (36, 1), (45, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (30, 1), (36, 1), (41, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (32, 1), (36, 1), (38, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(20, 1), (45, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (39, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(39, 1), (62, 1)] }, { coefficient := 1, powers := [(49, 1), (62, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB2_7.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB2_7
