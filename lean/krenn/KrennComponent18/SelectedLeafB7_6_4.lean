import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0607988f1ffccab22fd7286dc8f99fda7c6bc6bcfc76fef3f1796fa1df6ba170"
def certificateSHA256 : String := "0120f49b782d6eaf920843c2680268c6f71b5663a14dddd72b284963ec7b0fa6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 667 := ![
  10,
  11,
  15,
  17,
  19,
  143,
  167,
  168,
  301,
  318,
  432,
  433,
  437,
  440,
  442,
  443,
  449,
  478,
  618,
  657,
  659,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (21, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1), (38, 1), (52, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (38, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (38, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -2, powers := [(24, 1), (38, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (48, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (29, 1), (38, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (31, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (26, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (38, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (29, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (31, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (26, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_6_4.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_6_4
