import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f95f556063c2027991727c0d0bdf0d0ed55b44ec67ea2b134e9125573318b1a1"
def certificateSHA256 : String := "4f26b80913733f317c7c8022f8fcabcf30ff43be578f788910da8b937ad6b3dc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 641 := ![
  0,
  2,
  189,
  196,
  197,
  202,
  349,
  350,
  359,
  442,
  460,
  464,
  471,
  473,
  499,
  502,
  550,
  556,
  557,
  582,
  620,
  634,
  635,
  637,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (27, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (55, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (22, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (28, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (27, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (27, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (17, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (24, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 2), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (24, 1), (28, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (19, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 2), (19, 1), (37, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 2), (19, 1), (38, 1), (45, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 2), (38, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (24, 1), (28, 1), (38, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (37, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (43, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (45, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 2), (19, 1), (38, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 2), (19, 1), (38, 1), (59, 1), (60, 1)] }],
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB1_4.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB1_4
