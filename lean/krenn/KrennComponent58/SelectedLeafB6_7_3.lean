import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB6_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "92c4e1c87963289c4f638b033b3f1cb13ffefb9c37d700655cd9fc11830deb1c"
def certificateSHA256 : String := "cf7c232af9f7d559975d43461a2490c08fbf1638cf87c23f1f92fb982c1b703e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 622 := ![
  8,
  10,
  11,
  25,
  29,
  30,
  31,
  39,
  40,
  192,
  201,
  225,
  241,
  253,
  339,
  340,
  352,
  353,
  355,
  474,
  509,
  527,
  561,
  562,
  612,
  613,
  615,
  616,
  617,
  618,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (40, 1), (46, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (40, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (40, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (40, 1), (58, 1), (61, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (28, 1), (40, 1), (44, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (40, 1), (44, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (40, 1), (44, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (31, 1), (40, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (40, 1), (52, 1), (59, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (40, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (40, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (40, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (40, 1), (45, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (31, 1), (40, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (40, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (40, 1), (58, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (40, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (40, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (40, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (40, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (38, 1), (40, 1), (55, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (40, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (40, 1), (46, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (39, 1), (40, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(40, 2), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (46, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (40, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (40, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (28, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (28, 1), (40, 1), (58, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (28, 1), (40, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (40, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (28, 1), (40, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB6_7_3.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB6_7_3
