import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_4_6_5_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "757c14509560671ad4fa0500436a1d46863b70ab6f90d0c4ef42b7bae6da2ea8"
def certificateSHA256 : String := "cdf8e54028656ee908d91a59fb9e373292be0cd4976e20de9a4325fca98ca9e6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 677 := ![
  9,
  23,
  166,
  167,
  170,
  299,
  302,
  314,
  316,
  408,
  436,
  440,
  588,
  661,
  666,
  667,
  670,
  671,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(31, 1), (50, 1), (67, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_4_6_5_6.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_4_6_5_6
