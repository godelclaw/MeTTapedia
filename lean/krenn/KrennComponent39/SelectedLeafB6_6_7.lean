import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB6_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "686ce098b75b6972f36540ab028c3efd525121b452a24997e0939b36c369ebbf"
def certificateSHA256 : String := "4768523622baecc899041647851c58ef338d16da3e4e1d3ecb016b24c80773c4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 670 := ![
  1,
  3,
  4,
  6,
  7,
  9,
  32,
  184,
  193,
  263,
  315,
  317,
  430,
  434,
  440,
  566,
  651,
  654,
  660,
  662,
  663,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (46, 1), (57, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (27, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (57, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (57, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (57, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (22, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (57, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (57, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (57, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (57, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (57, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (57, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (27, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (57, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (57, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (54, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1), (57, 1), (67, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (27, 1), (46, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (27, 1), (43, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (46, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (42, 1), (46, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1), (57, 1), (67, 1)] }, { coefficient := 2, powers := [(15, 1), (22, 1), (49, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (49, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (43, 1), (49, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := -2, powers := [(40, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 2), (67, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (57, 1), (67, 1)] }, { coefficient := -2, powers := [(15, 1), (26, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (22, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB6_6_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB6_6_7
