import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case858Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "615fdbccaa10033a0feebc9fe8d062bb80d0b129fc5a71cdd4bcbdb8ad67a51b"
def sourceSystemSemanticSHA256 : String := "994ef68ebe7589dc3041cbd07bf7c4f1ea0c6aac8e5a4b3c03485d656abc5058"
def certificateSHA256 : String := "6596095a24f9f4d8e3bdb5928e90291871c00a336d36cb9ff41effeaa0e63a38"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 16 → Fin 675 := ![
  0,
  39,
  41,
  414,
  416,
  421,
  422,
  423,
  424,
  425,
  659,
  661,
  663,
  668,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(13, 1), (32, 1), (37, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (40, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (43, 1), (45, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (43, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (15, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (29, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly]
  ring

theorem selectedHasNoCommonZero {R : Type*}
    [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case858Selected.selectedHasNoCommonZero

end Krenn.X5Case858Selected
