import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB4_3_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6abf7d29da74041822e7d12612b96fa8592a269c9369bd7dca416d23294ff59d"
def certificateSHA256 : String := "22ead633b2d02322117e8c4c75b471822f462fa7965a923faf499d7d32e8d2c0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 620 := ![
  9,
  23,
  33,
  34,
  35,
  212,
  247,
  251,
  316,
  337,
  338,
  341,
  349,
  461,
  471,
  497,
  499,
  610,
  613,
  615,
  619
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 62) := ![
  [{ coefficient := 2, powers := [(3, 1), (22, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (22, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (43, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (16, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := -1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(3, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(35, 1), (57, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component59.SelectedLeafB4_3_2.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB4_3_2
