import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f12b0c9067eb6540dc6490f41e3baae20a4cd036deae28bcaff87f059823b582"
def certificateSHA256 : String := "5aaa49b82ac7a38c76164eb91a3c7ccefcfb4c0474559a31f8ceeda05c31bf7d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 673 := ![
  0,
  2,
  15,
  17,
  18,
  19,
  23,
  24,
  128,
  153,
  161,
  167,
  307,
  323,
  326,
  417,
  452,
  457,
  461,
  462,
  471,
  503,
  504,
  536,
  663,
  664,
  667,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (49, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (38, 1), (41, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (41, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (31, 1), (38, 1), (41, 1), (53, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (41, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (41, 1), (54, 1), (58, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (45, 1), (55, 1), (64, 1), (66, 1)] }, { coefficient := -2, powers := [(26, 1), (31, 1), (41, 1), (49, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (41, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (41, 1), (48, 1), (61, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (46, 1), (49, 1), (55, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (34, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (41, 1), (46, 1), (55, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (34, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (41, 1), (54, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (41, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (34, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (46, 1), (49, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (41, 1), (46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1), (54, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(31, 1), (41, 1), (49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (41, 1), (55, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (41, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(31, 1), (41, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1), (41, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (41, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (41, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (41, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (25, 1), (41, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (31, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (41, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (41, 1), (46, 1), (49, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (41, 1), (53, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (26, 1), (41, 1), (54, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (41, 1), (45, 1), (55, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (26, 1), (31, 1), (41, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1), (41, 1), (48, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (25, 1), (41, 1), (46, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (31, 1), (41, 1), (54, 1), (64, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_6_1.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_6_1
