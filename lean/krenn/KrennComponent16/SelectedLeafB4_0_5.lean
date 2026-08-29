import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB4_0_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ff188814f8f33fc8d56a051d625558d627f70c905b87eb3bc2234a3b9ba3de8b"
def certificateSHA256 : String := "d2783d46e56b9e7f46d84e5093a6725c72f9cb5b6ec2bf7ebbfcb385a7578da6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 671 := ![
  9,
  13,
  23,
  166,
  167,
  170,
  247,
  248,
  250,
  298,
  302,
  314,
  316,
  408,
  436,
  440,
  448,
  594,
  661,
  662,
  664,
  666,
  667,
  668,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (58, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(25, 1), (48, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (50, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (55, 1), (58, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (25, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (45, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (58, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(50, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (21, 1), (25, 1), (55, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (26, 1), (55, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 2), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (31, 1), (50, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (37, 1), (40, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB4_0_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB4_0_5
