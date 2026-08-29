import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_2_5_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4c73a42b62d291f89f88cb0b8308f4456c89c340ea2a9b688327246e3c5a54fb"
def certificateSHA256 : String := "b1bff442e6e7f97522032f694ea1382efe930efaf133b517ac4b7e71f3dd1cc4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 676 := ![
  180,
  181,
  184,
  187,
  191,
  192,
  195,
  301,
  303,
  321,
  324,
  347,
  419,
  425,
  434,
  440,
  460,
  463,
  465,
  470,
  471,
  618,
  620,
  637,
  645,
  660,
  663,
  666,
  669,
  670,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (26, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (17, 1), (19, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (45, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (46, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (46, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_2_5_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_2_5_2
