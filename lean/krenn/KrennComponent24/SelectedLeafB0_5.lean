import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB0_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5cdb7e11d553300f10d1f104f5411e75fcf2ebbd29a6f95a677eb21c562f4dac"
def certificateSHA256 : String := "9e89331e2800e5e48ecd74c9ca7817f2ff2eb863364d587d7846c12034869f99"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 670 := ![
  2,
  15,
  23,
  148,
  153,
  160,
  164,
  166,
  167,
  196,
  259,
  260,
  282,
  300,
  307,
  316,
  323,
  333,
  417,
  425,
  430,
  441,
  457,
  462,
  471,
  484,
  488,
  571,
  597,
  663,
  664,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (49, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(31, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 2, powers := [(18, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (31, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (31, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(18, 1), (31, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (48, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(18, 1), (26, 1), (31, 1), (43, 1), (45, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (31, 1), (43, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB0_5.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB0_5
