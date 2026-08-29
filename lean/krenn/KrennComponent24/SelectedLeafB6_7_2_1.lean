import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB6_7_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0a29f97d3e3bdf605ccfb073ffae77b959e3cda98a02e169dfff2a8d38b51686"
def certificateSHA256 : String := "ca93669a053681f0fe2f1007737091e96acbc526b8154b72ff2c47b0c5a598c6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 676 := ![
  2,
  15,
  23,
  160,
  161,
  176,
  282,
  300,
  307,
  323,
  430,
  452,
  457,
  462,
  471,
  585,
  663,
  664,
  666,
  672,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (14, 1), (21, 1), (31, 1), (60, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (55, 1), (60, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (14, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (25, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (68, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (14, 1), (31, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (49, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (14, 1), (21, 1), (24, 1), (31, 1), (60, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (25, 1), (55, 1), (60, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (14, 1), (31, 1), (49, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (18, 1), (25, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (31, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (31, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (25, 1), (42, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (31, 1), (42, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 2, powers := [(3, 1), (14, 1), (21, 1), (31, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB6_7_2_1.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB6_7_2_1
