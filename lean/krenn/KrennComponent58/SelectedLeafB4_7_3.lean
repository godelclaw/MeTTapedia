import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB4_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e91f5e4b5a95248bff86cb398d40bb076dee214de82589f52ecd7c84c95bf0d0"
def certificateSHA256 : String := "03d70508454f1b9ac2c11029e70f69481dff635ab38cea8071c208b0537918e5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 622 := ![
  11,
  29,
  30,
  31,
  37,
  38,
  192,
  195,
  201,
  220,
  339,
  340,
  342,
  353,
  438,
  467,
  474,
  508,
  573,
  612,
  613,
  615,
  616,
  620,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(9, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(14, 1), (28, 1), (46, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (40, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (51, 1), (54, 1), (55, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (51, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (54, 2), (55, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1), (55, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (52, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [(38, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 2, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (14, 1), (28, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (28, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (24, 1), (54, 2), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (24, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (51, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (51, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (28, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB4_7_3.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB4_7_3
