import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ecc83dab14acfcb149e185daf5eb6eb1bbf953a62fda04b9b88ea2839d63798e"
def certificateSHA256 : String := "6844573db8dc1cc736f75c14feae43bee302cae9a6ae9630019ec2a46513eedf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 590 := ![
  29,
  194,
  196,
  198,
  199,
  209,
  226,
  227,
  233,
  234,
  256,
  257,
  335,
  341,
  342,
  348,
  349,
  361,
  362,
  365,
  366,
  390,
  473,
  489,
  510,
  542,
  543,
  583,
  584,
  586,
  587,
  588,
  589
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(12, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (32, 1), (44, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (32, 1), (53, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (32, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(29, 1), (41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (39, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (54, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (39, 1), (43, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (36, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (48, 1), (54, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (48, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (48, 1), (54, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (32, 1), (43, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (21, 1), (32, 1), (54, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (32, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (32, 1), (54, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (26, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (49, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (39, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (21, 1), (32, 1), (48, 1), (54, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (32, 1), (48, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (32, 1), (48, 1), (54, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (38, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(38, 1), (57, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (25, 1), (32, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (3, 1), (5, 1), (32, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 2), (5, 1), (32, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (25, 1), (32, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (26, 1), (32, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (39, 1), (54, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (32, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (29, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (21, 1), (25, 1), (32, 1), (48, 1), (54, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (25, 1), (32, 1), (48, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (25, 1), (32, 1), (48, 1), (54, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (32, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (54, 1), (58, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB4_5
