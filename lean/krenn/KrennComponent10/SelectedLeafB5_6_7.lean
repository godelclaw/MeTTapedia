import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB5_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6d7a078ce0b36960fbc7512a1e5ce82223beb28bf749c818f1ab0ce5fee7df38"
def certificateSHA256 : String := "15d82743253cbf16f5553b3c2609ea2f199c526ea3500879cb24aa4fbb36d549"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 644 := ![
  2,
  5,
  8,
  19,
  21,
  162,
  163,
  164,
  170,
  181,
  197,
  290,
  349,
  350,
  359,
  363,
  369,
  446,
  463,
  466,
  556,
  557,
  568,
  582,
  634,
  635,
  638,
  640,
  641,
  642,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (44, 1), (45, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(23, 1), (40, 1), (56, 1)] }, { coefficient := 3, powers := [(23, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(23, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (44, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (24, 1), (40, 2), (43, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (40, 1), (43, 1), (48, 1), (53, 1), (55, 1), (66, 1)] }, { coefficient := 2, powers := [(2, 1), (36, 1), (40, 1), (43, 1), (48, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (24, 1), (40, 1), (43, 1), (45, 1), (53, 1), (66, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (24, 1), (43, 1), (45, 1), (53, 1), (55, 1), (66, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (36, 1), (43, 1), (45, 1), (53, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (24, 1), (40, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (40, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(2, 1), (36, 1), (40, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (40, 1), (48, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (45, 2)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (36, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (19, 1), (40, 1), (48, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (40, 1), (48, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (45, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (24, 1), (45, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (45, 1), (56, 1), (64, 1)] }, { coefficient := -3, powers := [(23, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (45, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (40, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (45, 1)] }, { coefficient := 3, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (24, 1), (40, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (45, 1)] }, { coefficient := -1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (24, 1), (40, 2), (48, 1), (53, 1), (66, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (40, 1), (48, 1), (53, 1), (55, 1), (66, 1)] }, { coefficient := -2, powers := [(2, 1), (36, 1), (40, 1), (48, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (40, 1), (45, 1), (53, 1), (66, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (45, 1), (53, 1), (55, 1), (66, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (36, 1), (45, 1), (53, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (19, 1), (40, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (24, 1), (40, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (24, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (40, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (40, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (40, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (24, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (24, 1), (45, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (23, 1), (45, 1), (56, 1)] }, { coefficient := 3, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (19, 1), (24, 1), (40, 2), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (24, 1), (40, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (36, 1), (40, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (29, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (40, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (36, 1), (45, 1), (53, 1), (58, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB5_6_7.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB5_6_7
