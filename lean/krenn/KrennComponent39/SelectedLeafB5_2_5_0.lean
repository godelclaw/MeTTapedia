import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_5_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fdf8670de1e22c2d05fac619eefc5305dbd869b3402cbca44ceeaa68bf15721b"
def certificateSHA256 : String := "97aa0e34a6615ed0b46d44acc52ee947895d7fe4b063dbc4cc83f5fd8e75640f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 673 := ![
  191,
  193,
  300,
  301,
  319,
  324,
  350,
  396,
  422,
  425,
  440,
  451,
  452,
  510,
  566,
  581,
  623,
  625,
  660,
  663,
  666,
  668,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (51, 2), (65, 1)] }, { coefficient := 1, powers := [(51, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (49, 1), (51, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (49, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (42, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (47, 1), (49, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (42, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (42, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (51, 2), (65, 1)] }, { coefficient := -1, powers := [(42, 1), (51, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (42, 1), (49, 1), (59, 2)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (42, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (47, 1), (49, 1), (59, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_5_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_5_0
