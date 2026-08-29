import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB6_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5698e6d6f8ab4a340162eb75475bc916b3f55cf5cece6aa92157707190f2e77a"
def certificateSHA256 : String := "0d5205b407b170f0a385bb68bf8df7209597647c6e3af68ce3e09aa4f2b8e27b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 673 := ![
  2,
  13,
  15,
  23,
  129,
  148,
  160,
  176,
  307,
  323,
  324,
  452,
  457,
  462,
  471,
  504,
  663,
  665,
  666,
  669,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(3, 1), (25, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (18, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(5, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (30, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB6_2_2.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB6_2_2
