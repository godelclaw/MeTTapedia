import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_4_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0bc70bb5091a29ca417d51e1cce48b3a70629e20e979596451f1cae9128745e7"
def certificateSHA256 : String := "240f602791e6ca51c1a8de495601854a86644313bd71c5817c5acb855bbf16ba"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 673 := ![
  8,
  9,
  11,
  12,
  14,
  15,
  16,
  23,
  128,
  161,
  282,
  305,
  306,
  307,
  323,
  327,
  430,
  448,
  452,
  457,
  462,
  471,
  503,
  585,
  589,
  596,
  606,
  607,
  616,
  624,
  653,
  661,
  663,
  666,
  668,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (29, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (24, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1), (45, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(31, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1), (40, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (20, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (32, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (20, 1), (29, 1), (49, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (26, 1), (29, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (29, 1), (49, 1), (50, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (29, 1), (32, 1), (38, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (20, 1), (24, 1), (49, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (24, 1), (26, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (24, 1), (49, 1), (50, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (32, 1), (38, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (61, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (47, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (38, 1), (40, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (45, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (40, 1), (51, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (44, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (20, 1), (49, 1), (55, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (26, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (50, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (32, 1), (38, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (35, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (20, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (44, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (35, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (44, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (20, 1), (44, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (26, 1), (44, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (38, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (41, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (32, 1), (38, 1), (44, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (32, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (20, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (6, 1), (32, 1), (35, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (15, 1), (26, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (20, 1), (35, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (15, 1), (20, 1), (26, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (26, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (34, 1), (38, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (29, 1), (40, 1), (45, 1), (60, 1)] }, { coefficient := 2, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(14, 1), (37, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (26, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (34, 1), (38, 1), (40, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1), (45, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (38, 1), (40, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (35, 1), (41, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (41, 1), (44, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (6, 1), (32, 1), (35, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (26, 1), (32, 1), (44, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (20, 1), (26, 1), (44, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_4_4.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_4_4
