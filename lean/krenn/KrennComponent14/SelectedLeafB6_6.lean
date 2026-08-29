import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8895524d8e6db5487e8352afc0109c77d6a44db8c0c9abe7678c387f022db795"
def certificateSHA256 : String := "982c97bb196a66736a40733d8fc22e14a9934e64968a165a2c2d058448b949ef"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 640 := ![
  9,
  11,
  12,
  20,
  23,
  90,
  122,
  132,
  162,
  167,
  179,
  192,
  194,
  195,
  244,
  282,
  309,
  313,
  345,
  348,
  349,
  350,
  351,
  368,
  395,
  406,
  502,
  524,
  555,
  633,
  635,
  636,
  637,
  638,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (31, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (25, 1), (28, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (31, 1), (37, 1), (49, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (44, 1), (49, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (51, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (17, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (17, 1), (28, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (17, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (42, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (42, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (46, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (31, 1), (37, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (44, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (28, 1), (44, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(45, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (30, 1), (31, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (31, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }]
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
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB6_6.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB6_6
