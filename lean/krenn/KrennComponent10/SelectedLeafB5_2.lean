import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB5_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3856a22208f656c6f6d9298e841e0558caee90b41aad2339333c98b957ec19fc"
def certificateSHA256 : String := "14cc20432c8fbe046f998c898fbc1f9d555c45368c55aa8e61b40bca8befcda8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 641 := ![
  1,
  4,
  19,
  20,
  21,
  29,
  31,
  226,
  241,
  348,
  349,
  350,
  359,
  362,
  383,
  384,
  406,
  463,
  466,
  576,
  577,
  586,
  632,
  634,
  635,
  637,
  638,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (29, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (44, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (27, 1), (30, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (30, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (30, 1), (36, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (22, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (22, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 2), (22, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (22, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (13, 1), (24, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (35, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (18, 1), (24, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (35, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (32, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (24, 1), (35, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (18, 1), (24, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (32, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 2), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(23, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (24, 1), (35, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (18, 1), (24, 1), (32, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (24, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (18, 1), (24, 1), (32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 2), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (27, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (19, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 2), (27, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (27, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (27, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (27, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (44, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (30, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (30, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (30, 1), (35, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (29, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (29, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (29, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (30, 1), (36, 1), (42, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB5_2.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB5_2
