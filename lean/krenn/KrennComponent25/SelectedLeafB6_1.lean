import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b68acb24fc58809f085286a08ec5dece59b499888f5cbccd5d248d03206497f7"
def certificateSHA256 : String := "336b918a3d8ce0387f5c4f78e303d687d68a455c6a03deb24fdb4582f9149b54"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 662 := ![
  6,
  10,
  11,
  12,
  21,
  146,
  147,
  148,
  149,
  150,
  175,
  257,
  294,
  312,
  319,
  353,
  363,
  423,
  424,
  450,
  469,
  578,
  579,
  586,
  609,
  655,
  656,
  657,
  658,
  660,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (34, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (20, 1), (47, 1), (59, 1), (61, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (20, 1), (47, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (20, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (26, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (20, 1), (34, 1), (35, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (17, 1), (34, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (47, 1), (59, 1), (61, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (47, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (34, 1), (35, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (34, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (32, 1), (34, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (32, 1), (34, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (52, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (12, 1), (34, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (52, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (34, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (52, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (17, 1), (34, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (50, 1), (52, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (47, 1), (50, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (34, 1), (35, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (47, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (48, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (4, 1), (5, 1), (32, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (7, 1), (32, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (50, 1), (52, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB6_1
