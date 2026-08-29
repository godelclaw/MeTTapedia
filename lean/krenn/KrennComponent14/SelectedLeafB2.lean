import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "626a913da6177a95d22e8efbfc0e84420c24225fdb9de39d8d44f68726db4133"
def certificateSHA256 : String := "89425ca00753ef8802541ecc4f4a949f027da81113c901cbc74e55cfe47023a5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 637 := ![
  8,
  9,
  10,
  11,
  18,
  19,
  20,
  27,
  127,
  161,
  162,
  163,
  164,
  189,
  190,
  194,
  195,
  245,
  309,
  348,
  349,
  350,
  351,
  352,
  457,
  460,
  464,
  465,
  524,
  555,
  572,
  575,
  576,
  581,
  605,
  631,
  633,
  634,
  635,
  636
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (35, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(34, 1), (35, 1), (40, 1), (41, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (40, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (23, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (34, 1), (40, 1), (41, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (17, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (40, 1), (41, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (25, 1), (31, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (25, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (25, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (25, 1), (27, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (19, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (28, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (21, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (28, 1), (40, 1), (49, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (40, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (40, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (32, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (32, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (21, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(21, 1), (23, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (21, 1), (45, 1), (59, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (40, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (40, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (34, 1), (35, 1), (40, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (35, 1), (40, 1), (41, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (35, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (28, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (45, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (45, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (40, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (38, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (40, 1), (41, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (40, 1), (42, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (40, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(23, 1), (38, 1), (40, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB2.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB2
