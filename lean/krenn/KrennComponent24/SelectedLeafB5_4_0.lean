import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_4_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0a971bf0a765e72d95ada1ca07fe3b3a3f9f482d4dc97980b19396b3e8e42889"
def certificateSHA256 : String := "5148d5bdb7a8eeece066113f539742574f7aaceb9d64ba39c231df314c4042c6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 673 := ![
  15,
  23,
  128,
  153,
  154,
  161,
  259,
  282,
  299,
  300,
  301,
  307,
  316,
  321,
  323,
  328,
  333,
  417,
  425,
  430,
  452,
  455,
  457,
  462,
  471,
  588,
  663,
  664,
  668,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (45, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (24, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(21, 1), (30, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(21, 1), (30, 1), (47, 1), (55, 1)] }, { coefficient := 2, powers := [(24, 1), (49, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(25, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(31, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(21, 1), (30, 1), (55, 1)] }, { coefficient := 2, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(30, 1), (55, 1)] }, { coefficient := -1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (21, 1), (30, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (31, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (31, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (21, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(20, 1), (21, 1), (30, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(21, 1), (30, 1), (55, 1)] }, { coefficient := -2, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -2, powers := [(26, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (21, 1), (30, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (20, 1), (21, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (21, 1), (30, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (25, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (24, 1), (26, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (26, 1), (30, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (20, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (31, 1), (49, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (24, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_4_0.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_4_0
