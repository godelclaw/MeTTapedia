import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_2_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "256d741f408a43de716ddb0c15abebd3736201ed303d38f27796a90b01941100"
def certificateSHA256 : String := "d8848e25d491b33bf8972de496f11b99a5ec82299a511f96984bff9e64753724"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 675 := ![
  10,
  14,
  15,
  18,
  19,
  134,
  157,
  158,
  298,
  301,
  307,
  319,
  320,
  323,
  363,
  440,
  443,
  448,
  451,
  453,
  465,
  471,
  475,
  584,
  612,
  662,
  665,
  668,
  670,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1)] }, { coefficient := -1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (32, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (35, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (29, 1), (45, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (35, 1), (38, 1), (45, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (38, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (45, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (45, 2), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (45, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (29, 1), (45, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (45, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (47, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 2), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (54, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (45, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (54, 2), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(52, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (23, 1), (45, 2), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (45, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (45, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (66, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (66, 2)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (46, 1), (52, 1), (54, 1), (64, 2)] }, { coefficient := 1, powers := [(25, 2), (46, 1), (52, 1), (64, 2)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (40, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (23, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (66, 2)] }, { coefficient := -1, powers := [(25, 1), (46, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (54, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (43, 1), (46, 1), (52, 1), (54, 1), (64, 2)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (46, 1), (52, 1), (64, 2)] }, { coefficient := 1, powers := [(28, 1), (43, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [(40, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(43, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (29, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (46, 1), (52, 1), (54, 1), (64, 2)] }, { coefficient := -1, powers := [(25, 1), (46, 1), (52, 1), (64, 2)] }, { coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := 1, powers := [(45, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (43, 1), (46, 1), (52, 1), (54, 1), (64, 2)] }, { coefficient := -1, powers := [(24, 1), (29, 1), (46, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 2), (43, 1), (46, 1), (52, 1), (64, 2)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (29, 1), (66, 2)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (43, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (46, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(29, 1), (66, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (38, 1), (45, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (41, 1), (45, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (43, 1), (45, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (43, 1), (47, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (35, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (29, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (45, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (45, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (43, 1), (46, 1), (52, 1), (54, 1), (64, 2)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (29, 1), (46, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 2), (43, 1), (46, 1), (52, 1), (64, 2)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (28, 1), (29, 1), (66, 2)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (28, 1), (43, 1), (54, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (28, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (29, 1), (46, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (40, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (43, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (46, 1), (52, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (45, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (29, 1), (45, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (35, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (35, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (46, 1), (52, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (28, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (46, 1), (52, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (28, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (25, 1), (40, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (25, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1), (64, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_2_1_5.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_2_1_5
