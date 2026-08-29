import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB0_3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0464941e819e82f0f0532a5780dc42210bc8a0d6905d8665a8283589cdc9e23b"
def certificateSHA256 : String := "4e5ee3c8e422456752a5a85e947989f8a5a8d5f6d95b119867c4f46a57498f66"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 667 := ![
  18,
  21,
  54,
  97,
  135,
  137,
  146,
  147,
  149,
  151,
  153,
  154,
  158,
  160,
  187,
  223,
  224,
  227,
  293,
  295,
  296,
  301,
  302,
  311,
  315,
  316,
  318,
  404,
  407,
  437,
  444,
  453,
  454,
  457,
  465,
  470,
  471,
  473,
  476,
  550,
  557,
  578,
  588,
  589,
  609,
  610,
  657,
  658,
  660,
  662,
  663,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (39, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (39, 1), (43, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (53, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (38, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (41, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(22, 1), (41, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (13, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (53, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (55, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (41, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (23, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (27, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (22, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (27, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (44, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (38, 1), (56, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (35, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (43, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (44, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (38, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (41, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (41, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (41, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (48, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (27, 1), (39, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 2), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (39, 1), (43, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1), (45, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (22, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (22, 1), (53, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB0_3_7.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB0_3_7
