import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB4_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a850768244f60f4b1463c243b3c86514a055282e9aa76d468352d82704102790"
def certificateSHA256 : String := "266ff9e6a2bd07d6dd2ab7f5eacc5e302b8dbee3bfd08ffba9ceedc5b155c70c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 641 := ![
  8,
  10,
  11,
  19,
  21,
  161,
  162,
  163,
  184,
  185,
  190,
  343,
  349,
  350,
  356,
  359,
  369,
  446,
  456,
  463,
  466,
  473,
  550,
  634,
  635,
  637,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 2, powers := [(29, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (43, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(23, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (32, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (32, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (24, 1), (43, 1), (52, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB4_4.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB4_4
