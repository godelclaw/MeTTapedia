import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component48.SelectedLeafB6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ac19817983d56cf42c0a00115ae567a234fe09e3e17f3510a7a60bb889e88a7f"
def certificateSHA256 : String := "9cdd2cd11868349ca67b300d17574d7b54bcc51ba58e1dade015e2ae6798300e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 641 := ![
  4,
  5,
  24,
  30,
  162,
  239,
  259,
  348,
  359,
  360,
  364,
  385,
  464,
  560,
  634,
  635,
  637,
  638,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := -1, powers := [(40, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(42, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (48, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component48.SelectedLeafB6_7.selectedHasNoCommonZero

end Krenn.Component48.SelectedLeafB6_7
