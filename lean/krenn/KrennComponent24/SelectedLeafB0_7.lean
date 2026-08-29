import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB0_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "eb753048f40653fa56b45f01ae86a96ea5b882330d454a59abe0fc9625b93250"
def certificateSHA256 : String := "85d303fc68d215e5621a1596ea6a74c261379a4764c350e8bc7691f947fb0d53"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 670 := ![
  2,
  15,
  23,
  50,
  132,
  146,
  153,
  159,
  160,
  164,
  166,
  167,
  196,
  259,
  307,
  316,
  323,
  457,
  463,
  471,
  584,
  597,
  652,
  663,
  664,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (46, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (49, 1), (51, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (26, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (26, 1), (34, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (34, 1), (39, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (34, 1), (42, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (34, 1), (46, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (49, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB0_7.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB0_7
