import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_2_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "27ee88a6862f800e54efb229d9e79abc7f33d8c0917ff8ea837c4e5b2ece646f"
def certificateSHA256 : String := "c2614efa799790a14c57e94b3ecdecc2a26b7ab2c4622231eb3d220c45bbd41a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 670 := ![
  9,
  15,
  26,
  179,
  180,
  181,
  279,
  297,
  316,
  433,
  438,
  450,
  454,
  541,
  566,
  657,
  660,
  663,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 67) := ![
  [{ coefficient := -2, powers := [(19, 1), (24, 2), (26, 1), (47, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 2), (25, 1), (44, 1), (46, 1), (55, 2), (66, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 2), (44, 1), (55, 2), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (19, 1), (24, 2), (26, 1), (46, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (19, 1), (24, 1), (39, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (24, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (19, 1), (24, 1), (55, 2)] }, { coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (19, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 2), (46, 1), (55, 2)] }],
  [{ coefficient := 2, powers := [(8, 1), (19, 1), (24, 2), (46, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (19, 1), (24, 2), (61, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (55, 2)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 2), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (19, 1), (24, 1), (61, 1)] }, { coefficient := -2, powers := [(19, 2), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 2), (46, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -4, powers := [(19, 1), (24, 1), (39, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (49, 1), (55, 2)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (19, 1), (24, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (19, 1), (24, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (19, 1), (24, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (20, 1), (24, 2), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (24, 2), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (19, 1), (24, 2), (26, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (24, 2), (26, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (47, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (24, 2), (25, 1), (44, 1), (46, 1), (55, 2)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (24, 2), (44, 1), (55, 2)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (19, 1), (24, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (19, 1), (24, 1), (42, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (19, 1), (24, 1), (48, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (24, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (24, 1), (44, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (24, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (24, 1), (39, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (24, 1), (49, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 2), (24, 1), (48, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_2_2_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_2_2_6
