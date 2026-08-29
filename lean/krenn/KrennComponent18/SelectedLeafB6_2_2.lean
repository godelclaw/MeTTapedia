import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1ce5656e9a4c4df098c5d61ebc5f73b84d1c412b4111a09f273aac6b3cc64120"
def certificateSHA256 : String := "ea44415db7e02c5ed02ac22edbc1e744bfeeed5cbac1d23e65b31c8e67037d35"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 667 := ![
  7,
  9,
  10,
  15,
  19,
  143,
  295,
  301,
  318,
  437,
  443,
  562,
  657,
  658,
  659,
  660,
  663,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(31, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (31, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_2_2.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_2_2
