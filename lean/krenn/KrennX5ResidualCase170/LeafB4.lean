import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase170.LeafB4

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "e40ad60caa14e642f3d25817fe4ab1597c253457d11646b6b353b3e91de4a719"
def sourceSystemSemanticSHA256 : String := "20add63bf8b54e509595f0b1b998f4d29d4af04a6e7e2a0efe9a1752286bb95e"
def certificateSHA256 : String := "124f96a06cbd66f2c091e34d570a6ea0fc5cd0c750bd62357928d71d54b1d293"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 22 → Fin 678 := ![
  5,
  16,
  22,
  24,
  25,
  31,
  44,
  46,
  406,
  411,
  423,
  424,
  426,
  439,
  542,
  633,
  656,
  660,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(14, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (48, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (54, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (26, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (18, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (54, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (40, 1), (57, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (40, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (40, 1), (57, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (40, 1), (57, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(13, 1), (34, 1), (40, 1), (57, 1), (70, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase170.LeafB4.selectedHasNoCommonZero

end Krenn.X5ResidualCase170.LeafB4
