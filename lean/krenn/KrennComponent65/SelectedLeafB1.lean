import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6f70835cdcea57d8bbf9468c370010a4bfa43cc3ededdc97c1146823e5941ecd"
def certificateSHA256 : String := "378647c190bca19304981ab1c3c4548faa795ae27e1f326d20dc09011588c00c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 665 := ![
  2,
  3,
  6,
  7,
  8,
  9,
  12,
  15,
  26,
  29,
  199,
  203,
  212,
  302,
  304,
  318,
  320,
  423,
  440,
  477,
  540,
  610,
  611,
  661,
  662,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (40, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (34, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (31, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (34, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (31, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (34, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (40, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (34, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (46, 1), (49, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB1
