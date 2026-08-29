import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB4_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "293ce237a8d9eca4958fb21eabec68b6764dfb97a4a1f3993094bb14229828a1"
def certificateSHA256 : String := "4bf0c3db65db03d232e79077420b2f55accd0e0f81336600b70faff99aa0b90a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 622 := ![
  10,
  25,
  28,
  39,
  192,
  195,
  224,
  225,
  241,
  339,
  340,
  342,
  348,
  352,
  353,
  449,
  474,
  488,
  490,
  509,
  512,
  562,
  612,
  615,
  617,
  619,
  620,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(3, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (40, 1), (44, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (8, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (40, 1)] }, { coefficient := -1, powers := [(28, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (45, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (40, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB4_3_4.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB4_3_4
