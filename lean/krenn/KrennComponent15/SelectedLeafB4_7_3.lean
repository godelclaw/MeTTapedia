import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB4_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b464325250f2b8ef757c6d5bd2ba5d43dcbf61bffb88f135fccdc62b0c22ebb5"
def certificateSHA256 : String := "bb22f0b6866e5d056224f5e2372454bc9e65ef2b6c0bb91ae0fa0e01f3efc444"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 595 := ![
  20,
  26,
  37,
  43,
  230,
  340,
  363,
  364,
  385,
  386,
  545,
  546,
  584,
  587,
  591,
  594
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(11, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(24, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(24, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (40, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (43, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(34, 1), (55, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(37, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (52, 1)] }, { coefficient := -1, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (34, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB4_7_3.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB4_7_3
