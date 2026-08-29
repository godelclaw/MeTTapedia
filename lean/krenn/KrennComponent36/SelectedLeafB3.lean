import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "27557674f5fecc53f3fbfd83433d693e1361a6858ea5f86aa666facb9a92679f"
def certificateSHA256 : String := "7cdb4e0c1914156f9ca8b8e3f729879a8352215a1465ecd45c9edd5ca663fdc2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 666 := ![
  0,
  1,
  2,
  3,
  5,
  7,
  10,
  13,
  158,
  159,
  305,
  307,
  363,
  379,
  453,
  470,
  475,
  485,
  486,
  562,
  612,
  613,
  662,
  663,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (47, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (35, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (22, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (35, 1), (45, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB3
