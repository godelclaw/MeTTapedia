import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB5_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "afde77f5599c1b3d7685fa7db09596a451f7748b4d6d9b12930e59139eccd862"
def certificateSHA256 : String := "9738bc2703f7d2d3a5f5a6c63f137de0120bd05ee719ffaf73abcdb607d4e997"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 644 := ![
  4,
  5,
  19,
  21,
  24,
  29,
  164,
  167,
  284,
  349,
  350,
  359,
  363,
  364,
  406,
  463,
  466,
  557,
  634,
  635,
  638,
  640,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (48, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (35, 1), (39, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (39, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (39, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (35, 1), (39, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (39, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (39, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (48, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (39, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (39, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (19, 1), (35, 1), (39, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (29, 1), (39, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (39, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB5_6_5.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB5_6_5
