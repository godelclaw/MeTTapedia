import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_6_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9f92119a70b584d9c35f4567b8c19ff9b7d55b2e3a9f25aed7eaff68db7ca0e0"
def certificateSHA256 : String := "2f80db15fe28276289ee26872df5ebebe02b3c28b505e1e474e6d05298fbb7c4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 675 := ![
  7,
  10,
  18,
  20,
  22,
  171,
  191,
  196,
  200,
  275,
  288,
  302,
  318,
  319,
  402,
  418,
  420,
  424,
  429,
  442,
  470,
  565,
  567,
  662,
  663,
  668,
  670,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1)] }, { coefficient := 1, powers := [(32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(32, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(25, 1), (53, 1), (58, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (58, 1), (68, 1)] }, { coefficient := -2, powers := [(27, 1), (30, 1), (48, 1), (50, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (46, 1), (48, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(30, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(30, 1), (48, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (50, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 2, powers := [(30, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (21, 1), (46, 1), (50, 1), (55, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (21, 1), (50, 1), (55, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (21, 1), (31, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (27, 1), (30, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (46, 1), (48, 1), (50, 1), (55, 1), (67, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (49, 1), (50, 1), (55, 1), (67, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_6_3_4.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_6_3_4
