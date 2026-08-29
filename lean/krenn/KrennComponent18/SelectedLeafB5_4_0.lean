import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_4_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "00b9767fb7d7023edb681636e8aabaf79da1cfcac60ef330dd32512cae1c06af"
def certificateSHA256 : String := "919295acce62aafef34910e6f5a4a6c9ff926c98748b55eb69742e1175eaf84f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 667 := ![
  0,
  1,
  9,
  19,
  142,
  167,
  168,
  246,
  301,
  318,
  366,
  430,
  432,
  435,
  437,
  449,
  478,
  496,
  581,
  618,
  645,
  649,
  657,
  660,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (38, 1), (52, 1), (59, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (59, 2)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (31, 1), (38, 1), (52, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (24, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (24, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (24, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (38, 1), (45, 1), (52, 1), (59, 2)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (38, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (45, 1), (59, 2)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (38, 1), (45, 1), (52, 1), (59, 2)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (38, 1), (49, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (38, 1), (52, 2), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (37, 1), (38, 1), (52, 2), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (38, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (38, 1), (40, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (37, 1), (38, 1), (40, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (38, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (38, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (38, 1), (52, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1), (52, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (49, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (30, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (30, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (38, 1), (52, 1), (59, 2)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (59, 2)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (38, 1), (52, 1), (59, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (37, 1), (38, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (37, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (37, 1), (38, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (37, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (29, 1), (38, 1), (52, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (19, 1), (37, 1), (38, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (19, 1), (37, 1), (38, 1), (40, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (23, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (29, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (37, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (19, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 2), (37, 1), (38, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 2), (37, 1), (38, 1), (40, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (23, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (29, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (34, 1), (38, 1), (52, 1), (59, 2)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 2), (5, 1), (34, 1), (59, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (19, 1), (34, 1), (38, 1), (52, 1), (59, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (38, 1), (52, 1), (59, 1)] }]
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

#print axioms Krenn.Component18.SelectedLeafB5_4_0.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_4_0
