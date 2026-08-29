import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_6_3_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "74b6df28f488a14d05be5e7cac3161b0128507849529896f47162f80c8d35c1f"
def certificateSHA256 : String := "4dc029a5355d19bb689d3ad93f65d3363ddec6ab8281f5585d8d76eff5219fd4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 671 := ![
  20,
  22,
  68,
  143,
  152,
  168,
  301,
  302,
  436,
  443,
  556,
  582,
  583,
  593,
  655,
  658,
  659,
  661,
  663,
  664,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (26, 1), (52, 1), (57, 1), (63, 2), (66, 1)] }, { coefficient := 2, powers := [(9, 1), (24, 1), (54, 1), (57, 1), (63, 2), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (53, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (52, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (56, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (26, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (54, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (48, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (38, 1), (57, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (54, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (26, 1), (52, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (24, 1), (54, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (56, 1), (57, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (57, 2), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (35, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (24, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (32, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (24, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (57, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (48, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (47, 1), (50, 1), (57, 1), (63, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_6_3_4_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_6_3_4_3
