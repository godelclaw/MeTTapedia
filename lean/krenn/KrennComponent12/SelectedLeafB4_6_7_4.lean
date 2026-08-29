import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB4_6_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "aec01a891c284f45228f9f60c3884208d220ec59666ce4e50e886b84d30cd9b3"
def certificateSHA256 : String := "21cea7305bd3ef36ebb09640bd1367c72458e201e8bf04dc53fa333c7fefe64e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 625 := ![
  11,
  17,
  23,
  27,
  192,
  214,
  218,
  308,
  333,
  338,
  339,
  350,
  407,
  458,
  460,
  464,
  473,
  549,
  561,
  580,
  582,
  612,
  615,
  616,
  618,
  622,
  624
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(0, 1), (31, 1), (35, 1), (39, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (35, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (35, 1), (45, 1), (51, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (31, 1), (39, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (31, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (31, 1), (45, 1), (51, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (31, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (45, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (31, 1), (39, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (31, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (31, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (55, 1)] }, { coefficient := -2, powers := [(6, 1), (34, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(26, 1), (46, 1), (49, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 2, powers := [(26, 1), (46, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(52, 1)] }],
  [{ coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (39, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(6, 1), (47, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(37, 1), (58, 1)] }, { coefficient := -2, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (26, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (42, 1), (46, 1)] }, { coefficient := -2, powers := [(12, 1), (47, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB4_6_7_4.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB4_6_7_4
