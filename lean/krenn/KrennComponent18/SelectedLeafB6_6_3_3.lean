import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_6_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "90ccd93def7072011dc0f248f1c3cc78a2a85c8856e8c7da82ca8ca522c59ca0"
def certificateSHA256 : String := "989a2095f7f9dd72e8caea409ddbce7b807b2a3afa9a670825b367365fcfcebd"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 670 := ![
  0,
  9,
  10,
  19,
  147,
  294,
  295,
  301,
  318,
  323,
  409,
  437,
  438,
  443,
  479,
  496,
  497,
  625,
  657,
  658,
  660,
  663,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (31, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (28, 1), (40, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (40, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (40, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (28, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (26, 1), (33, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (36, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (33, 1), (49, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (36, 1), (49, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (45, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (45, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (45, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (28, 1), (40, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (40, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (40, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (20, 1), (28, 1), (31, 1), (52, 1), (59, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (20, 1), (31, 1), (33, 1), (52, 2), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (20, 1), (31, 1), (36, 1), (52, 2), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 2), (53, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 1), (53, 1), (56, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 2), (53, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1), (53, 1), (56, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (31, 1), (59, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (31, 1), (33, 1), (52, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (36, 1), (52, 1), (61, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (31, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (33, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (36, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (28, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (33, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (36, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (20, 1), (28, 1), (31, 1), (59, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (20, 1), (31, 1), (33, 1), (52, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (20, 1), (31, 1), (36, 1), (52, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1), (53, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1), (56, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1), (53, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (53, 1), (56, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (28, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (33, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (36, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (34, 1), (40, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (34, 1), (40, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (36, 1), (40, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (49, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (28, 1), (40, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (40, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (36, 1), (40, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (28, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (33, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (36, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(33, 1), (40, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (40, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (31, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (33, 1), (49, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (31, 1), (36, 1), (49, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (40, 1), (59, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (40, 1), (52, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (40, 1), (52, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(28, 1), (38, 1), (40, 1), (59, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (40, 1), (52, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (40, 1), (52, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (28, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (33, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (36, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (28, 1), (37, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (37, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (37, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (28, 1), (31, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (31, 1), (33, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (31, 1), (36, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (20, 1), (28, 1), (31, 1), (45, 1), (52, 1), (59, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (20, 1), (31, 1), (33, 1), (45, 1), (52, 2), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (20, 1), (31, 1), (36, 1), (45, 1), (52, 2), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (31, 1), (49, 1), (59, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (33, 1), (49, 1), (52, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (31, 1), (36, 1), (49, 1), (52, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (28, 1), (47, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (24, 1), (33, 1), (47, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (36, 1), (47, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (28, 1), (42, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (33, 1), (42, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (36, 1), (42, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (28, 1), (34, 1), (40, 1), (47, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (33, 1), (34, 1), (40, 1), (47, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (34, 1), (36, 1), (40, 1), (47, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (28, 1), (34, 1), (40, 1), (42, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (34, 1), (40, 1), (42, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (34, 1), (36, 1), (40, 1), (42, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (52, 2), (53, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (52, 1), (53, 1), (56, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 2), (53, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1), (53, 1), (56, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_6_3_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_6_3_3
