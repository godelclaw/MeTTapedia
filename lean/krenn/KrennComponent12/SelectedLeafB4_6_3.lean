import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB4_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "454ef491188c7cd4015861908d529fe21f949177acb44f747bfa70ff5b2e4358"
def certificateSHA256 : String := "42e95e7b8f240796879bd394e78b33ca99f859c48a9428885e5b0ad2d1bad310"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 622 := ![
  17,
  20,
  22,
  23,
  27,
  42,
  192,
  213,
  218,
  292,
  333,
  334,
  338,
  339,
  340,
  349,
  350,
  464,
  473,
  491,
  549,
  591,
  612,
  613,
  615,
  618,
  620
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 64) := ![
  [{ coefficient := 2, powers := [(28, 1), (47, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (51, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (28, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (50, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (51, 1), (54, 2), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (50, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (54, 2), (62, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (44, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (50, 1), (52, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (51, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (54, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (50, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (51, 1), (54, 2), (62, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (28, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1), (52, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (28, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (50, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 2), (62, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (28, 1), (54, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (50, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (44, 1), (47, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (17, 1), (28, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB4_6_3.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB4_6_3
