import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7c4cbec5ea86d4cf631d6f9181e76c5fd7f4975dbac61c03c60d2968b31e9443"
def certificateSHA256 : String := "f6c1d2e32699df52fb89c07934d5372b9972df45485aba0e247579d6f46fe155"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 661 := ![
  1,
  2,
  4,
  18,
  21,
  135,
  137,
  153,
  159,
  172,
  294,
  296,
  315,
  316,
  318,
  365,
  375,
  440,
  443,
  453,
  454,
  458,
  470,
  471,
  480,
  557,
  579,
  609,
  610,
  619,
  646,
  657,
  658,
  660
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 61) := ![
  [{ coefficient := 2, powers := [(2, 1), (24, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (18, 1), (33, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (30, 1), (41, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (19, 1), (33, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (33, 1), (45, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (24, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (18, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (30, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (34, 1), (52, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (23, 1), (34, 1), (52, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (45, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (34, 1), (45, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (34, 1), (45, 1), (55, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (22, 1), (34, 1), (52, 1), (55, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (16, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (18, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (18, 1), (36, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(8, 1), (30, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (33, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (33, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (53, 1)] }, { coefficient := 2, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (27, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (22, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (27, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (27, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (27, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(27, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (22, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(22, 1), (34, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (22, 1), (24, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(22, 1), (24, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(2, 2), (34, 1), (55, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (19, 1), (33, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (16, 1), (22, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (39, 1), (41, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (41, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (34, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (16, 1), (27, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (18, 1), (27, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (23, 1), (27, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(16, 1), (27, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (39, 1)] }, { coefficient := 2, powers := [(5, 1), (30, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (34, 1), (55, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (16, 1), (22, 1), (24, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (24, 1), (34, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(2, 2), (34, 1), (36, 1), (55, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 2), (34, 1), (45, 1), (52, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (16, 1), (22, 1), (24, 1), (35, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (16, 1), (22, 1), (24, 1), (38, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (16, 1), (22, 1), (24, 1), (43, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (16, 1), (22, 1), (43, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (16, 1), (27, 1), (45, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (18, 1), (27, 1), (34, 1), (45, 1), (50, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (23, 1), (27, 1), (34, 1), (45, 1), (50, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (39, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(2, 1), (39, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (30, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (19, 1), (33, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (33, 1), (43, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (45, 1), (51, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (24, 1), (34, 1), (35, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (24, 1), (34, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (24, 1), (34, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (34, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(16, 1), (27, 1), (34, 1), (45, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (23, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (39, 1), (41, 1), (43, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (39, 1), (44, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (33, 1), (43, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (30, 1), (41, 1), (43, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (30, 1), (44, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (19, 1), (33, 1), (43, 1), (48, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (30, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (33, 1), (43, 1), (45, 1), (48, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB1
