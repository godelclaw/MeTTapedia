import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_6_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c73e49abac7679b7a2bc7cc68420cab8f931ca1d381be9b5f29e1ad7cc3eb938"
def certificateSHA256 : String := "1d30c6bb5f4c8c143a03a5fa85b56d0c418e173c633dca9268dd776c2a69b1cd"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 676 := ![
  15,
  16,
  128,
  161,
  299,
  300,
  307,
  323,
  328,
  430,
  452,
  457,
  471,
  588,
  663,
  664,
  669,
  670,
  672,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (45, 1), (55, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (21, 1), (53, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (53, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (55, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (21, 1), (55, 1), (62, 2)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (21, 1), (55, 1), (62, 2)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (25, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (25, 1), (45, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (21, 1), (45, 1), (53, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (49, 1), (55, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (25, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (21, 1), (45, 1), (53, 1), (55, 1), (62, 2)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (62, 2)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (45, 1), (53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (48, 1), (51, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_6_6_0.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_6_6_0
