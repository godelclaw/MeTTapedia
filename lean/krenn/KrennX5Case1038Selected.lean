import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case1038Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "33c93ea07594b335b0a56461613f697e37497feb97c545099519f20ed65746c0"
def sourceSystemSemanticSHA256 : String := "178c62d9f4d1c77c084624d409e7a0a0c27f41921aef57465ee15a31ba948adc"
def certificateSHA256 : String := "19ec3be223a75de9b20ed1af852eb7047fe74b7afa1a2948e2b2d0f0c612be3a"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 32 → Fin 675 := ![
  0,
  1,
  3,
  7,
  10,
  14,
  16,
  17,
  22,
  24,
  28,
  38,
  39,
  47,
  391,
  399,
  403,
  407,
  414,
  416,
  422,
  423,
  425,
  439,
  604,
  606,
  639,
  659,
  661,
  662,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (66, 1)] }, { coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (40, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (40, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (34, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (34, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (23, 1), (43, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (23, 1), (43, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (43, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (15, 1), (43, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (16, 1), (43, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (43, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (43, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (35, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (41, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (30, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (30, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (30, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (30, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (30, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (34, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (34, 1), (35, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (34, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (23, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (15, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (16, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (38, 1), (48, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (41, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (35, 1), (48, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (41, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (35, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (38, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (35, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (41, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (15, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case1038Selected.selectedHasNoCommonZero

end Krenn.X5Case1038Selected
