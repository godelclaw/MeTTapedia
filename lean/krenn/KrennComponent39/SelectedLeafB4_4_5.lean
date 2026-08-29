import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "db4d77f495e7e9bb2b6be3ee540c367abf9df024b3a7b100093761cc158a336a"
def certificateSHA256 : String := "edef61f821a36882ec3e2488f7570c232f28088d482408271e8d1ab51a2264cb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 670 := ![
  181,
  187,
  188,
  189,
  191,
  250,
  277,
  300,
  301,
  302,
  303,
  313,
  315,
  316,
  382,
  383,
  397,
  417,
  419,
  425,
  430,
  434,
  463,
  470,
  647,
  654,
  660,
  661,
  663,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(22, 1), (45, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (43, 1), (49, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (42, 1), (54, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (45, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(22, 1), (49, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1), (57, 2), (64, 1)] }, { coefficient := -1, powers := [(22, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (49, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (42, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (45, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (52, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 2), (64, 1)] }, { coefficient := -1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (54, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (57, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (52, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (43, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (57, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (45, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (23, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (57, 2), (64, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (47, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (27, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (22, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (57, 2), (64, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (27, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(22, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (43, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (42, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (49, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (43, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(37, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 2), (64, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (22, 1), (32, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (22, 1), (23, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (19, 1), (27, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (22, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (31, 1), (37, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (23, 1), (27, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (31, 1), (37, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (18, 1), (22, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (23, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (57, 2), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (47, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (34, 1), (37, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (23, 1), (57, 2), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (28, 1), (47, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (34, 1), (37, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_4_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_4_5
