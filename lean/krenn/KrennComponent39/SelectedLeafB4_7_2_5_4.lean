import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_7_2_5_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2e35b813955775526e9a0fd042f837506d2ea737ac352050f89db067fc5aa3f6"
def certificateSHA256 : String := "c0653d4beb8b91d4bf20e3b97148306a2bc3ae624964376ec4ccedf5b3b4ef47"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 676 := ![
  19,
  26,
  68,
  268,
  304,
  305,
  318,
  476,
  515,
  602,
  603,
  659,
  662,
  664,
  666,
  668,
  671,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 69) := ![
  [{ coefficient := 2, powers := [(19, 1), (20, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (39, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (44, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (51, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (27, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (56, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (39, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (44, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (51, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (67, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(39, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (39, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (38, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (44, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (28, 1), (30, 1), (56, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (28, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (33, 1), (36, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (65, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_7_2_5_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_7_2_5_4
