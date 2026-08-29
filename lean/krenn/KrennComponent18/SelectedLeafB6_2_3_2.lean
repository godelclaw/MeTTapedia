import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_2_3_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b24ba1dd00d60cf253a39ef12051287b093d48fdb10ae25551ee99c945352a2c"
def certificateSHA256 : String := "ce34f8bb0ff5c88751d6714b93c2cd199c86bd88bf9ceba195cb348abf7e7a06"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 670 := ![
  0,
  19,
  168,
  294,
  318,
  323,
  437,
  496,
  497,
  562,
  625,
  657,
  660,
  663,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (33, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (36, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (33, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (36, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (45, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (45, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (45, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (45, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (33, 1), (45, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (36, 1), (45, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (52, 2), (53, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 2), (53, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (33, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (36, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(27, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (49, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (33, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (36, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (40, 1), (59, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (40, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (40, 1), (52, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (28, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (33, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (36, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (28, 1), (37, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (37, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (37, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1), (52, 2), (53, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (52, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 2), (53, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (45, 1), (48, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (33, 1), (45, 1), (48, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (33, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (36, 1), (45, 1), (48, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (36, 1), (49, 1), (52, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_2_3_2.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_2_3_2
