import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_3_3_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2e4d6aea767352b0d72684f031974c8e02bbbc29990f028085b6be4d18273038"
def certificateSHA256 : String := "45bd5160f4dfe1f5382a9f0c4b7f00005714e95c2caebfe777deacbd6f31b189"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 673 := ![
  18,
  134,
  135,
  138,
  146,
  153,
  295,
  302,
  407,
  440,
  453,
  454,
  480,
  557,
  579,
  588,
  589,
  619,
  657,
  658,
  660,
  662,
  665,
  667,
  669,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (53, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (56, 1), (58, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(52, 1), (58, 1), (59, 1), (66, 2)] }],
  [{ coefficient := -1, powers := [(16, 1), (45, 1), (53, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (56, 1), (58, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (48, 1), (56, 1), (58, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(33, 1), (45, 1), (50, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(33, 1), (45, 1), (53, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (56, 1), (58, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (45, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (33, 1), (45, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (33, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (33, 1), (45, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1), (61, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (58, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (59, 1), (66, 2)] }],
  [{ coefficient := -1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (48, 1), (56, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (58, 2), (59, 1), (66, 2)] }, { coefficient := 1, powers := [(36, 1), (58, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (58, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(39, 1), (44, 1), (52, 1), (58, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 1), (58, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(41, 1), (45, 1), (53, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (56, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (56, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (56, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (48, 1), (56, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (58, 2), (59, 1), (66, 2)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (46, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (39, 1), (44, 1), (58, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (45, 1), (58, 1), (59, 1), (66, 2)] }, { coefficient := -1, powers := [(17, 1), (38, 1), (39, 1), (58, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1), (48, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (58, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_3_3_4_3.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_3_3_4_3
