import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "41fd1fc53db8551de90f39ac760a327fbd0c9af6578ffbc331595026cb85b917"
def certificateSHA256 : String := "7666395a410e16ae086a643c4ae551e7feed0c12dcfceb8c11002ce09d49ccbf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 667 := ![
  7,
  9,
  10,
  15,
  19,
  143,
  162,
  163,
  167,
  168,
  295,
  301,
  315,
  318,
  327,
  409,
  433,
  437,
  443,
  562,
  584,
  657,
  658,
  659,
  660,
  662,
  663,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(2, 1), (31, 1), (49, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (48, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (26, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (21, 1), (24, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (17, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (24, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (47, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (17, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (45, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (13, 1), (31, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (13, 1), (31, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (24, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (19, 1), (24, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (24, 1), (25, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (8, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (31, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (45, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 2), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (34, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (24, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_4_2.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_4_2
