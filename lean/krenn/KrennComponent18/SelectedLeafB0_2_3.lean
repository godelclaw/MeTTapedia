import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB0_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f016c781dce08e3d6608f0ec4abe4bf4462631b5b10b36043c5d223916520ed1"
def certificateSHA256 : String := "f5144fede66f36616f6267b76aace193c60baccd5c94116539050dad5f9277a3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 667 := ![
  1,
  7,
  9,
  10,
  19,
  84,
  159,
  168,
  170,
  301,
  317,
  318,
  366,
  425,
  437,
  440,
  443,
  466,
  562,
  580,
  591,
  618,
  645,
  657,
  658,
  660,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (31, 1), (59, 2)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (31, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (31, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (29, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (29, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (31, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (31, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 2), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(25, 1), (31, 1), (42, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(25, 1), (31, 1), (42, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(25, 1), (31, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(25, 1), (31, 1), (46, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (53, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (26, 1), (29, 1), (52, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (29, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (29, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (56, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(6, 2), (31, 1), (59, 2)] }, { coefficient := 2, powers := [(6, 1), (25, 1), (31, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (25, 1), (31, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (31, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (56, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (17, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (13, 1), (31, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (31, 1), (49, 1), (52, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (31, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1)] }, { coefficient := -1, powers := [(25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (37, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (37, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (37, 1), (46, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (31, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (31, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (34, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (31, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (31, 1), (46, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (29, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (29, 1), (46, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (52, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (56, 2), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 2), (18, 1), (31, 1), (59, 2)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (37, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (25, 1), (31, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (25, 1), (31, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (30, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (30, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (31, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (34, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (29, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (29, 1), (56, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB0_2_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB0_2_3
