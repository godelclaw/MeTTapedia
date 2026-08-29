import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_2_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "de24274044b3a5975e47bbedb336cd297b32acba3917dbfcdf8fdcfb2489a2cc"
def certificateSHA256 : String := "f68df3e9c93ea3158064b247bc180496529c23a87c700ff205da022c262742dc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 675 := ![
  9,
  10,
  12,
  15,
  16,
  19,
  24,
  164,
  272,
  276,
  302,
  305,
  307,
  375,
  448,
  451,
  497,
  607,
  608,
  661,
  662,
  664,
  665,
  668,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (31, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (34, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (34, 1), (37, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (29, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (35, 1), (38, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (31, 1), (45, 1), (48, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (34, 1), (40, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (35, 1), (38, 1), (45, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (35, 1), (38, 1), (40, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (34, 1), (37, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (35, 1), (37, 1), (38, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (29, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (34, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (43, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (31, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (34, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (32, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (34, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (34, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1), (37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (40, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1)] }, { coefficient := -1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (41, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (38, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (26, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (35, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (34, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (34, 1), (35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (23, 1), (26, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (23, 1), (31, 1), (40, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (23, 1), (34, 1), (40, 2), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (26, 1), (32, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (32, 1), (38, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (34, 1), (38, 1), (40, 2)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (34, 1), (38, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (23, 1), (34, 1), (37, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (32, 1), (34, 1), (37, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 2)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 2)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (13, 1), (26, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (26, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (29, 1), (34, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (31, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (34, 1), (35, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (29, 1), (34, 1), (37, 1), (48, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (34, 1), (35, 1), (37, 1), (38, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_2_1_3.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_2_1_3
