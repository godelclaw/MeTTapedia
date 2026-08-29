import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB1_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0f3580e3cede5dad879e458cfca015281b1a1c4129082175e35dcc1fb1512d6b"
def certificateSHA256 : String := "7a6ccd16a73dc3948340b333c5592d1b1faf0edb4312560027c9f229c5eb28c7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 670 := ![
  2,
  23,
  153,
  166,
  167,
  307,
  323,
  425,
  470,
  471,
  472,
  503,
  504,
  518,
  541,
  584,
  585,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(25, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (30, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (30, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (30, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (29, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 2), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (26, 1), (30, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (30, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (42, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (46, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (38, 1), (42, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (38, 1), (42, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (30, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (30, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (38, 1), (46, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB1_7.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB1_7
