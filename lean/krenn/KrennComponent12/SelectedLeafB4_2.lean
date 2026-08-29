import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "705396ab3a8db5d95926890c209d5c20ccfb48cd41deef2fccac996b3a0e8460"
def certificateSHA256 : String := "352a7cb9237398fc34fd9603fa763b298ea0ad62d9a381a1ab1f041d19f0404d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 619 := ![
  11,
  17,
  20,
  22,
  23,
  27,
  192,
  213,
  218,
  292,
  333,
  334,
  338,
  339,
  340,
  350,
  458,
  460,
  464,
  473,
  549,
  561,
  580,
  582,
  612,
  613,
  615,
  618
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 61) := ![
  [{ coefficient := -2, powers := [(0, 1), (31, 1), (35, 1), (39, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (35, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (35, 1), (45, 1), (51, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (31, 1), (39, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (31, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (31, 1), (45, 1), (51, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (31, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (45, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (31, 1), (39, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (31, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (31, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 4, powers := [(28, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 4, powers := [(19, 1), (28, 1), (59, 1)] }, { coefficient := 2, powers := [(22, 1), (23, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(22, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -4, powers := [(22, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 4, powers := [(17, 1), (22, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (51, 1)] }],
  [{ coefficient := -4, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (44, 1), (51, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -4, powers := [(12, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(52, 1)] }],
  [{ coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (28, 1), (59, 1)] }, { coefficient := -2, powers := [(28, 1)] }],
  [{ coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (39, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -4, powers := [(5, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(37, 1), (58, 1)] }, { coefficient := -2, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (17, 1), (28, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB4_2.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB4_2
