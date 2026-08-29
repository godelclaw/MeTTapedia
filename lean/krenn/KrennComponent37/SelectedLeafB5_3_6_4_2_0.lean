import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_6_4_2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "936a0324a669bf3a0c6de73577e3a97bf3cedd36fa3246fe5ea2dac416584758"
def certificateSHA256 : String := "fa54b486d11a66a80ab19bbbb01095fe29e97292759200a5fb1bd19249dfc2db"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 676 := ![
  22,
  154,
  298,
  299,
  311,
  315,
  410,
  430,
  439,
  453,
  455,
  478,
  479,
  484,
  487,
  500,
  565,
  590,
  596,
  604,
  605,
  645,
  648,
  656,
  659,
  660,
  663,
  667,
  668,
  673,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := 1, powers := [(4, 1)] }],
  [{ coefficient := 1, powers := [(5, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (41, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (41, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (41, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1), (41, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1), (46, 1), (60, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (21, 1), (41, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (46, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 2), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (41, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (41, 1), (46, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(37, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (21, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (41, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (41, 2), (51, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (22, 1), (41, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (21, 1), (41, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (41, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (41, 1), (46, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (46, 2), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (38, 1), (41, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 2), (42, 1), (51, 1), (57, 1), (65, 2)] }, { coefficient := -1, powers := [(21, 1), (41, 2), (46, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 2), (48, 1), (51, 1), (53, 1), (65, 2)] }, { coefficient := -1, powers := [(21, 1), (41, 2), (51, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (46, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(37, 1), (41, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(37, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(37, 1), (41, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (38, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (41, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (46, 1), (51, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (48, 1), (51, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (46, 1)] }, { coefficient := -1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (35, 1), (41, 2), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (22, 1), (41, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (37, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (41, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (37, 1), (60, 2)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (41, 1), (46, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (37, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (41, 2), (48, 1), (51, 1), (65, 2)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (41, 2), (42, 1), (51, 1), (65, 2)] }, { coefficient := -1, powers := [(15, 1), (37, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (29, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1), (35, 1), (41, 1), (53, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (37, 1), (46, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (41, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (41, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (41, 2), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (41, 1), (51, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (35, 1), (41, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1), (60, 2)] }, { coefficient := -1, powers := [(32, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(35, 1), (37, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(35, 1), (37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (51, 1), (60, 1), (63, 1), (65, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_6_4_2_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_6_4_2_0
