import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_2_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9f09dffef02100247e85e072205a2e6de303b4352b937cf1145bc1734f374843"
def certificateSHA256 : String := "671b873ffacf3bce8310bf1629deac5700e1a83d2db7a5af443ccb315e3daa1b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 670 := ![
  18,
  21,
  135,
  137,
  150,
  151,
  153,
  158,
  224,
  252,
  294,
  301,
  302,
  311,
  337,
  390,
  408,
  441,
  444,
  454,
  557,
  598,
  657,
  660,
  663,
  664,
  665,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (46, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (23, 1), (51, 1), (56, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (41, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (51, 1), (56, 1), (66, 1)] }, { coefficient := -2, powers := [(23, 1), (27, 1), (46, 1), (51, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (23, 1), (24, 1), (64, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (22, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(27, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (56, 1)] }, { coefficient := -2, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (46, 1), (51, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (22, 1), (23, 1), (51, 1), (52, 1), (56, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (41, 1), (51, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (51, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := 2, powers := [(23, 1), (27, 1), (46, 1), (51, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (54, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(45, 1), (48, 1), (54, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (13, 1), (18, 1), (22, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (56, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (27, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (22, 1), (23, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (27, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (48, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_2_5_7.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_2_5_7
