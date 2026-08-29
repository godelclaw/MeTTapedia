import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_4_0_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e8b1e47f065036d2aadcd7d787a8cb24ace7fcc14e84cbec26fda1a3629b31b4"
def certificateSHA256 : String := "2de49fed36c609f10ede0a7a70a125e80264a5489a9f82cf5fd6af70ff810dd9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 674 := ![
  4,
  9,
  13,
  23,
  31,
  142,
  166,
  167,
  175,
  298,
  299,
  302,
  314,
  316,
  317,
  321,
  408,
  440,
  448,
  503,
  585,
  588,
  661,
  662,
  666,
  667,
  669,
  670,
  671,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (50, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (45, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (22, 1), (45, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (50, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (31, 1), (50, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (34, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (47, 1), (50, 1), (55, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_4_0_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_4_0_5
