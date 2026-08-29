import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component56.SelectedLeafB2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2219e012c7a931580d6c702a8e7dbb8b55df338866e3f2da270f8c14730d9a57"
def certificateSHA256 : String := "069355f711e30f0816e440a8f4e756843172caf92838ecda904d41ee231cec9e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 589 := ![
  9,
  11,
  17,
  209,
  235,
  236,
  237,
  241,
  242,
  263,
  365,
  372,
  373,
  527,
  528,
  575,
  585,
  586,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 58) := ![
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (26, 1), (29, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 2), (53, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (26, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (29, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 2), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (21, 1), (29, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 2), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (21, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (29, 1), (32, 1), (38, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 2), (38, 2)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (37, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (37, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (17, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(17, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (16, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (12, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (32, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (29, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (29, 1), (37, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (29, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (32, 1), (34, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (32, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (32, 1), (42, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (35, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (38, 1), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (44, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (35, 1), (38, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (38, 2), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (38, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := 1, powers := [(38, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }]
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
    (values : Fin 58 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component56.SelectedLeafB2.selectedHasNoCommonZero

end Krenn.Component56.SelectedLeafB2
