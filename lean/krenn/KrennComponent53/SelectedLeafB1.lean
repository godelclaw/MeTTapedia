import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component53.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "54da2cb25bd24946ec5191ddc329095f6f60018f50ca4364ef9e6faaff4db3a1"
def certificateSHA256 : String := "492dabb6bb9a990868518a559359aba44bd2d8b791fce71adbfe0d789ccb28ba"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 640 := ![
  2,
  4,
  27,
  201,
  208,
  212,
  214,
  216,
  221,
  230,
  359,
  360,
  445,
  458,
  463,
  474,
  477,
  491,
  559,
  636,
  637,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (38, 1), (59, 2)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (38, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (38, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (38, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (38, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (38, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (25, 1), (38, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (27, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (27, 1), (38, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (43, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (46, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (38, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (38, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (38, 1), (47, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (38, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (48, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (38, 1), (43, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (27, 1), (38, 1), (42, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (27, 1), (38, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (38, 1), (42, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (38, 1), (46, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component53.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component53.SelectedLeafB1
