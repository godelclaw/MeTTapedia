import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_6_1_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3bc874372c00eb85a67f5a2265ff2321c0990a87ff8cbd5bd158f03415819285"
def certificateSHA256 : String := "429911530bf9e4dedaa54a7caec9973c59242184f13d4b022dae9570479d4daa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 670 := ![
  10,
  15,
  19,
  143,
  162,
  168,
  246,
  294,
  318,
  323,
  403,
  409,
  437,
  440,
  443,
  458,
  562,
  580,
  608,
  657,
  658,
  659,
  660,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (37, 1), (57, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (57, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (34, 1), (38, 1), (52, 2), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (38, 1), (48, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (57, 2), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (46, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (46, 1), (53, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (46, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (34, 1), (38, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (48, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (46, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (57, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 2), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (57, 2), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (20, 1), (34, 1), (38, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (34, 1), (38, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (34, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (34, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (34, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (46, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (45, 1), (46, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (34, 1), (38, 1), (52, 2), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (47, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (34, 1), (38, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (42, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (45, 1), (48, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (49, 1), (57, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_6_1_0.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_6_1_0
