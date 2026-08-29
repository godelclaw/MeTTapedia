import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB6_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9179ce07fa3c5edc0e2cd812d5913af4030ea4a0521f729ccd1666d7a4380e5a"
def certificateSHA256 : String := "5639b81add9559c25af048d93bb9c8727f4b8e05b43b7a902a88690643566cff"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 622 := ![
  8,
  10,
  11,
  25,
  30,
  31,
  39,
  40,
  192,
  201,
  224,
  225,
  339,
  340,
  348,
  353,
  355,
  474,
  527,
  562,
  612,
  613,
  615,
  616,
  617,
  618,
  620,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (46, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (38, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (38, 1), (58, 1), (61, 2), (63, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (46, 1), (51, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (31, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (38, 1), (52, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (38, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (31, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (38, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (38, 1), (58, 1), (61, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (38, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (38, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (38, 1), (46, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (39, 1), (46, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (38, 1), (46, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (38, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (38, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (38, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (46, 1), (52, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (38, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (38, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (38, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (38, 1), (46, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (28, 1), (38, 1), (58, 1), (61, 2)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (38, 1), (52, 1), (59, 1), (61, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB6_6_1.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB6_6_1
