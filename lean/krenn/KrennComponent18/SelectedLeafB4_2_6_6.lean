import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_2_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2b87d8b6b0423b406d8d44d7a7aea09eb8dd40f94ce2ac550b5b02c5da138694"
def certificateSHA256 : String := "147015ce229b0d5829b1bafcf087d24358f1de80379ebd84a4b076ef6faf0f0a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 670 := ![
  0,
  10,
  13,
  19,
  161,
  168,
  179,
  318,
  437,
  443,
  496,
  562,
  625,
  657,
  660,
  663,
  664,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (33, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (36, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (24, 1), (26, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (26, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (24, 1), (52, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (24, 1), (56, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (33, 1), (49, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (36, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (45, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (45, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (45, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (49, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (52, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1), (56, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (45, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (33, 1), (45, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (36, 1), (45, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (45, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (45, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (33, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (36, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (49, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (49, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (24, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (33, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (36, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (40, 1), (59, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (40, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (40, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (40, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (40, 1), (56, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (28, 1), (37, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (33, 1), (37, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (37, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (37, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (37, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (24, 1), (52, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (24, 1), (54, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (28, 1), (43, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (33, 1), (43, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (36, 1), (43, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (43, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (43, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (36, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (36, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (34, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (34, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (24, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (24, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (36, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (36, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (45, 1), (48, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (33, 1), (45, 1), (48, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (33, 1), (49, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (36, 1), (45, 1), (48, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (36, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (45, 1), (48, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (45, 1), (48, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (49, 1), (56, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_2_6_6.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_2_6_6
