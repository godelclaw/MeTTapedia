import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_6_7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2f6f3f48ff243aad0c1ba31452fabf9ebe4f535ceac7a0005d322721c524277f"
def certificateSHA256 : String := "b7704f1d97d9d7cc7a25ace88159b9c7b5a7367d97092b0ffd641e3d96ff6fe3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 675 := ![
  24,
  139,
  276,
  298,
  302,
  303,
  320,
  465,
  497,
  522,
  591,
  593,
  607,
  608,
  661,
  664,
  666,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(7, 1), (43, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (34, 1), (37, 1), (45, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1), (45, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (37, 1), (45, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (45, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 1)] }, { coefficient := -1, powers := [(21, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(19, 1), (37, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(45, 1), (52, 1)] }, { coefficient := -1, powers := [(46, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (34, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (21, 1), (37, 1), (60, 2)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (34, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (34, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (21, 1), (37, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (34, 1), (37, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (34, 1), (37, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (37, 1), (43, 1), (45, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (43, 1), (45, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (21, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (34, 1), (37, 1), (40, 2)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (34, 1), (37, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (39, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (45, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_6_7_0.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_6_7_0
