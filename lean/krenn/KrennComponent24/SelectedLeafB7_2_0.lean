import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cfd71b26d4c30aee1a2c052829cfeeefd224b3ce5072f5e5881ee63d95bf1c64"
def certificateSHA256 : String := "ec6c293f33d4fae276f71a6d291f6b2784420492ed66c3ab8c36d49af7f05b9d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 673 := ![
  13,
  15,
  23,
  129,
  153,
  259,
  282,
  301,
  307,
  316,
  323,
  417,
  457,
  462,
  471,
  588,
  663,
  664,
  665,
  666,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (22, 1), (37, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (22, 1), (25, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (22, 1), (45, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (22, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (37, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (25, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (45, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (49, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (31, 1), (49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (31, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (31, 1), (49, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (31, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (31, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (31, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (37, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (25, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (8, 1), (37, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (31, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (14, 1), (20, 1), (31, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (26, 1), (31, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 2), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (34, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (25, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_2_0.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_2_0
