import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7b7ec7e173e7775dd860f96e6cc4154202c6f0d26dfcd09f68a539116ae57e34"
def certificateSHA256 : String := "583bd3fa9fc6bc501da7e94d3456015a99c2508b41fa7db8b7410ef291596bce"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 669 := ![
  0,
  1,
  3,
  10,
  13,
  160,
  305,
  307,
  453,
  470,
  480,
  562,
  583,
  613,
  651,
  662,
  663,
  664,
  665,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (29, 1), (43, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1), (50, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (50, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (50, 1), (57, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (29, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (23, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (24, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (45, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (45, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (41, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (41, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1), (45, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (57, 2), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1), (47, 1), (50, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (29, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (23, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (29, 1), (47, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (47, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (48, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB2_3.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB2_3
