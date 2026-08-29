import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case427Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "e0584ab471361ec11657fa4430001531ea1f3e46a4a87ad32886ceb16e076f6b"
def sourceSystemSemanticSHA256 : String := "878caa3d048eb00c3bfa3dc2966f0519218c9aca7ebbcca19d5cd41490d4c717"
def certificateSHA256 : String := "21225a0ec0ac42a31f988fc7c45a2f1ef9bf0f5a3b755dd54023d2319d66b845"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 18 → Fin 675 := ![
  0,
  1,
  2,
  3,
  24,
  25,
  43,
  388,
  415,
  422,
  423,
  424,
  425,
  426,
  433,
  659,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (35, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (24, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (24, 1), (40, 1), (46, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (24, 1), (43, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (24, 1), (46, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (40, 1), (41, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (69, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (16, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (16, 1), (40, 1), (46, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (16, 1), (43, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (16, 1), (46, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (26, 1), (46, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (34, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(26, 1), (34, 1), (37, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (18, 1), (46, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (34, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (37, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (46, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case427Selected.selectedHasNoCommonZero

end Krenn.X5Case427Selected
