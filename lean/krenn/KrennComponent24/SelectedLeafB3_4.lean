import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f0a5b25e6967dbc93b071c5117295bfd9146ff4a29a39ee444e26bd39c4603dc"
def certificateSHA256 : String := "ec7a7753afd5f9d0d2fe2e24ac9e8293e04aa2850ad747725e51acc76d0178cc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 670 := ![
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
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 65) := ![
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
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(25, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (63, 1)] }, { coefficient := -1, powers := [(29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 2), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (26, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (26, 1), (30, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (30, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (46, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (30, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (30, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (38, 1), (46, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (38, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (38, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB3_4.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB3_4
