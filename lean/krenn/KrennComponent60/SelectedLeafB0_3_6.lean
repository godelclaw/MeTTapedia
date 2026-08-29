import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB0_3_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "723cf599406a85cdb7b18a965b84bcb84a19fb478f4843f9924db172d788ef1e"
def certificateSHA256 : String := "65f7de8d1d539b046e98a3bea74eac1834c988007fde11848418fca5e2f49bd6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 665 := ![
  22,
  25,
  44,
  86,
  145,
  168,
  169,
  177,
  195,
  237,
  264,
  293,
  301,
  302,
  310,
  316,
  404,
  434,
  443,
  467,
  556,
  592,
  609,
  655,
  656,
  658,
  660,
  662,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (54, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(41, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (25, 1), (29, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (51, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1), (54, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (21, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (29, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (25, 1), (29, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1), (47, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB0_3_6.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB0_3_6
