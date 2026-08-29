import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component48.SelectedLeafB6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5775f73bc98dd2c269eddbcb5974d08ce35398908bd730e6dd5bceaf8c2939a2"
def certificateSHA256 : String := "521c137ef9791d5ef359c4b4cc1700a5a4a66a2cb39ec3987d097c2b268daa8c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 641 := ![
  2,
  4,
  23,
  26,
  161,
  162,
  173,
  196,
  197,
  228,
  239,
  241,
  319,
  348,
  356,
  359,
  360,
  404,
  434,
  435,
  438,
  463,
  472,
  478,
  484,
  556,
  634,
  635,
  637,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (58, 2)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (29, 1), (52, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (45, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (50, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(21, 1), (33, 1), (37, 1), (50, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(21, 1), (33, 1), (37, 1), (50, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (45, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (33, 1), (37, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (37, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (45, 2)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (45, 2)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (37, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (45, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(21, 1), (33, 1), (37, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(21, 1), (33, 1), (37, 1), (46, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (45, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (48, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (52, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (33, 1), (37, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (33, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (25, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (58, 2)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (50, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (33, 1), (37, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (33, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (33, 1), (37, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (37, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (37, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (33, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (33, 1), (37, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (39, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1), (39, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (33, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (33, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (25, 1), (33, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (20, 1), (24, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 2), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (25, 1), (33, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 2), (33, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (33, 1), (37, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (21, 1), (33, 1), (37, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (21, 1), (33, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (25, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (25, 1), (33, 1), (37, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (25, 1), (33, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 2), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (36, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 2), (8, 1), (36, 1), (58, 2)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (25, 1), (36, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (36, 1), (45, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component48.SelectedLeafB6_0.selectedHasNoCommonZero

end Krenn.Component48.SelectedLeafB6_0
