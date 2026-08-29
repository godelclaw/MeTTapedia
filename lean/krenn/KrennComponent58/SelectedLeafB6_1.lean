import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "740ba5daf466f9a4ca2b9f530389ab9e5037da22b0f5e511eb9ae7183c55b5d1"
def certificateSHA256 : String := "8b347d9c4289bc55e88eba96c3505eaaddc145f220fdc649cd9dfa838e941de0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 619 := ![
  10,
  38,
  227,
  339,
  342,
  353,
  359,
  459,
  474,
  482,
  488,
  507,
  561,
  562,
  582,
  584,
  612,
  613,
  615,
  617,
  618
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (35, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (35, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (35, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (31, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (31, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (34, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (35, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (35, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (35, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (35, 1), (48, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (25, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (25, 1), (48, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (48, 1), (54, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (35, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (24, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (24, 1), (35, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (31, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (31, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (24, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (24, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (31, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (31, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (24, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (24, 1), (54, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (52, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (52, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (52, 1), (54, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (35, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (54, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (35, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (54, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (35, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (54, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (61, 1)] }, { coefficient := -1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(50, 1)] }, { coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (54, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (43, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (40, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (40, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (40, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (40, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (40, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (40, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (40, 1), (54, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (31, 1), (35, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (31, 1), (35, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (14, 1), (24, 1), (35, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (14, 1), (24, 1), (35, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (25, 1), (31, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (25, 1), (31, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (31, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (14, 1), (24, 1), (25, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (14, 1), (24, 1), (25, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (14, 1), (24, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (20, 1), (31, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (20, 1), (31, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (14, 1), (20, 1), (24, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (14, 1), (20, 1), (24, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (50, 1)] }, { coefficient := -1, powers := [(25, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB6_1
