import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB4_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8f130f1ee7f15d243d2f0f048cad626e38c4e511eaa9436b122a6f19c1670b7f"
def certificateSHA256 : String := "d7f9c2a1b61280b7b74eebcd424deddf69f8d8e92a6265f438cb9e1d46ab6d19"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 671 := ![
  12,
  19,
  23,
  24,
  26,
  29,
  193,
  196,
  254,
  275,
  301,
  309,
  310,
  315,
  411,
  414,
  420,
  421,
  423,
  434,
  440,
  540,
  581,
  582,
  607,
  610,
  645,
  661,
  662,
  664,
  665,
  667,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 2), (31, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 2), (34, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (44, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (36, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (39, 1), (45, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (50, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (28, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (28, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (13, 1), (36, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (44, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (18, 1), (36, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (44, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (18, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 2), (28, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (28, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (39, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (28, 1), (39, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1)] }, { coefficient := -2, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (44, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (28, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (28, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (39, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (39, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (39, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (39, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (37, 1), (44, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (40, 1), (44, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (44, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (34, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (28, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (34, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (28, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (39, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 3), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (13, 1), (19, 1), (23, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 2), (13, 1), (19, 1), (28, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (23, 1), (44, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (28, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (19, 1), (23, 1), (39, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (19, 1), (28, 1), (39, 1), (47, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (44, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (19, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (19, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (25, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (57, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB4_6_1.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB4_6_1
