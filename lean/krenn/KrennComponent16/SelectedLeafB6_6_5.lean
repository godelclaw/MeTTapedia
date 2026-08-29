import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB6_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5ea993c13766d005b65844d061b4fe7269d73d4b5013480e7635681643fb78a3"
def certificateSHA256 : String := "d453928320f7256c24cef6eac9fe394fc612488cbad7d8b5aef61952b66b14e9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 671 := ![
  1,
  3,
  9,
  13,
  23,
  247,
  248,
  250,
  302,
  316,
  440,
  448,
  594,
  661,
  663,
  664,
  667,
  668,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (56, 1), (58, 1), (63, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (56, 1), (58, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (56, 1), (58, 1), (63, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (55, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (56, 1), (58, 1), (61, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1), (58, 2), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (56, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (21, 1), (37, 1), (40, 1), (56, 1), (58, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (56, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB6_6_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB6_6_5
