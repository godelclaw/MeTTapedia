import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B2N1W14NonzeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "53c9ae7d69b3fa354aef87bd7073e73e0c85d0caba56467ce125add4a8f959e7"
def certificateSHA256 : String := "eaff1d96cbf077cefbc9e48085a51ce024348438a633c9e16206de4ea83a6bcb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 575 := ![
  68,
  105,
  106,
  107,
  183,
  270,
  310,
  438,
  459,
  487,
  515,
  564,
  571,
  572,
  574
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (39, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (42, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (60, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(7, 1), (42, 1), (45, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (48, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (48, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (45, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (44, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (45, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (40, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B2N1W14NonzeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3B2N1W14NonzeroCertificate
