import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_2_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "47e46fc1cd1a5c15388e0a3da621bcb8edea898a4022b73b534cac97c0c8d198"
def certificateSHA256 : String := "e0f1c1c76f00e2451178d2c3d12d80db5bced455b114a283598ac758d5570173"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 676 := ![
  15,
  23,
  128,
  160,
  161,
  282,
  300,
  307,
  323,
  430,
  452,
  457,
  462,
  471,
  588,
  663,
  664,
  669,
  672,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (21, 1), (55, 1), (62, 2), (67, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (21, 1), (31, 1), (62, 2), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (25, 1), (55, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (21, 1), (55, 1), (62, 2), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (55, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (31, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (55, 1), (62, 2)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (31, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (55, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (25, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (31, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (31, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (21, 1), (24, 1), (55, 1), (62, 2), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (21, 1), (24, 1), (31, 1), (62, 2), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (25, 1), (55, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (24, 1), (55, 1), (62, 2), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (24, 1), (55, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (49, 1), (55, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (31, 1), (49, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (25, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (31, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (21, 1), (45, 1), (55, 1), (62, 2)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (21, 1), (31, 1), (45, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (25, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (45, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (45, 1), (55, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_2_2_3.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_2_2_3
