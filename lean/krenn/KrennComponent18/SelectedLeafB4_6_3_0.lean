import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_6_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ed71c36a3d2f9a6f765c78e7ead11d87e0c3e4ca2dce2e49c66f9c470b1b8d1d"
def certificateSHA256 : String := "bc20a5b0ca16d91cf5cb9e9f822a9f9d64046e191a445f0a7c08051b4d796777"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 670 := ![
  10,
  19,
  162,
  168,
  246,
  294,
  317,
  318,
  319,
  323,
  403,
  409,
  437,
  440,
  443,
  458,
  562,
  564,
  580,
  591,
  608,
  657,
  658,
  660,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (37, 1), (38, 1), (52, 2), (54, 1)] }, { coefficient := -2, powers := [(20, 1), (37, 1), (38, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (38, 1), (54, 1), (56, 2)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (48, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (48, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (48, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (37, 1), (46, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (46, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (26, 1), (52, 2), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (52, 1), (53, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (45, 1), (48, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (37, 1), (46, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (26, 1), (52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (37, 1), (38, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (46, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (48, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (37, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (37, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (37, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (24, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (48, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (37, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (37, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (37, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (37, 1), (45, 1), (46, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (45, 1), (46, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (26, 1), (45, 1), (52, 2), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (45, 1), (52, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (37, 1), (38, 1), (52, 2), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (20, 1), (37, 1), (38, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (37, 1), (38, 1), (54, 1), (56, 2)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1), (38, 1), (48, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1), (38, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (45, 1), (46, 1), (48, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (47, 1), (48, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_6_3_0.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_6_3_0
