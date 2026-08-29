import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bb857a445fbb096bd2806e9643cba2c2729161ae4eb252a2b2554ea9668e4936"
def certificateSHA256 : String := "9b96c98cdc1b9677c7ec741a483717b55a3bd7759e01da0afbf354cb074c868c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 673 := ![
  2,
  11,
  13,
  15,
  16,
  23,
  129,
  161,
  282,
  307,
  323,
  452,
  457,
  461,
  462,
  471,
  503,
  504,
  663,
  665,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(25, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (49, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (22, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (31, 1), (38, 1), (53, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (38, 1), (57, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (49, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (48, 1), (61, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_2_6.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_2_6
