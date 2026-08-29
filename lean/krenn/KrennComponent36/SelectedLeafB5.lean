import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f485030a5c48f5da45ca74ca512ebf2f3f5580eea85a14decd8d2f16f3f1f3af"
def certificateSHA256 : String := "374e95315ee8bad1f39d2e952d1d539e2722c3232f144123961190b37370c252"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 666 := ![
  5,
  7,
  9,
  10,
  12,
  13,
  15,
  19,
  135,
  153,
  156,
  176,
  253,
  272,
  298,
  302,
  303,
  305,
  307,
  320,
  322,
  323,
  373,
  387,
  448,
  451,
  487,
  607,
  608,
  652,
  661,
  662,
  663,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (48, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (20, 1), (50, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (25, 1), (48, 1), (50, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (48, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (24, 1), (50, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (25, 1), (48, 1), (50, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (48, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (26, 1), (32, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (26, 1), (35, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (29, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (24, 1), (43, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (25, 1), (41, 1), (43, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (21, 1), (32, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (21, 1), (35, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (26, 1), (35, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (32, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (27, 1), (36, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (29, 1), (36, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(27, 1), (36, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (23, 1), (36, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(36, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (41, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (40, 1), (41, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (37, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (45, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (45, 1), (50, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (25, 1), (45, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (45, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (24, 1), (43, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (24, 1), (45, 1), (50, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (25, 1), (41, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (25, 1), (45, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (45, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (21, 1), (32, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (26, 1), (32, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (21, 1), (35, 1), (41, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (26, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (26, 1), (35, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (32, 1), (38, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB5
