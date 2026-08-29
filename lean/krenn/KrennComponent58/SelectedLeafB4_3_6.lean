import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB4_3_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a505f4f5d2412cbcf017f30215b87402c96ff302c55add3d2386eb46f7039ac5"
def certificateSHA256 : String := "114353c316bb3f0be17b8a973de558c3ccc1cb38e1230aa557932e6c62294358"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 622 := ![
  10,
  20,
  28,
  37,
  39,
  241,
  253,
  333,
  335,
  339,
  340,
  342,
  353,
  449,
  474,
  480,
  488,
  509,
  612,
  615,
  617,
  619,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 64) := ![
  [{ coefficient := -2, powers := [(6, 1), (24, 1), (39, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (39, 1), (46, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (28, 1), (39, 1), (40, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (40, 1), (44, 1), (60, 2), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (39, 1), (51, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (39, 1), (42, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (39, 1), (45, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (39, 1)] }, { coefficient := -1, powers := [(19, 1), (39, 1), (45, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (39, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (39, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (39, 1), (51, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (39, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (39, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (39, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (40, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (46, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (28, 1), (39, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(14, 1), (28, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (28, 1), (39, 1), (40, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1), (40, 1), (44, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 2), (40, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB4_3_6.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB4_3_6
