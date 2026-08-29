import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "28f1dce6ca7f200ea469a62f420cd3b9f996cd915d6daef86c01283bd881df50"
def certificateSHA256 : String := "4cc7b9dd9f83e48a65337bcae09831ce6520f467c96a2df0f123779de4407cbe"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 619 := ![
  10,
  23,
  25,
  37,
  38,
  193,
  220,
  221,
  225,
  227,
  241,
  333,
  339,
  340,
  342,
  348,
  352,
  353,
  438,
  449,
  474,
  507,
  508,
  612,
  613,
  614,
  615,
  616,
  617
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (22, 1), (24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(25, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (28, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (40, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [(38, 1), (40, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (28, 1), (40, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB6_5
