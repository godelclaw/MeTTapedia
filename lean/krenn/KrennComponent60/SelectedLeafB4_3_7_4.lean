import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_3_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ae413504f74a63eab6c2afa561e6d6a46bcebcfe20c9d58b093beec61588e656"
def certificateSHA256 : String := "e5171ed758d5ad5c1a9c3b49f1cb0741df8e602217496896e82fae7811ffe780"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 668 := ![
  22,
  143,
  164,
  165,
  172,
  263,
  292,
  294,
  295,
  301,
  302,
  315,
  436,
  443,
  464,
  556,
  592,
  593,
  655,
  656,
  658,
  660,
  663,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (26, 1), (43, 1), (45, 1), (67, 1)] }, { coefficient := -2, powers := [(24, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (26, 1), (43, 1), (45, 1), (50, 1), (61, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1), (43, 1), (45, 1), (50, 1), (67, 1)] }, { coefficient := 2, powers := [(24, 1), (43, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (50, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (43, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (46, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1), (26, 1), (43, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(41, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(41, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (43, 1), (45, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (43, 1), (45, 1), (50, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (41, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_3_7_4.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_3_7_4
