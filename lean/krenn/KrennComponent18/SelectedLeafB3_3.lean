import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ee451bf33c5dda804f7556298644791ed4884f8c052383ac5fcc32f6afaa4ad6"
def certificateSHA256 : String := "ed9b5b3d5c7404caec5c20ed6ad27a045d45b512f7821f4ae84f1fc8353f01cb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 664 := ![
  1,
  10,
  19,
  20,
  25,
  168,
  169,
  170,
  301,
  318,
  327,
  437,
  443,
  460,
  463,
  562,
  580,
  609,
  657,
  658,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (42, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (46, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (52, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (31, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (48, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (45, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (45, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (42, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (31, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (45, 1), (48, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB3_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB3_3
