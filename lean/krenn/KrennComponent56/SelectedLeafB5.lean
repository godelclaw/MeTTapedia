import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component56.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "db46c3c6f75a467e5e511fab631c9d45ed0537ec3c2737c679c02ec34c7349a5"
def certificateSHA256 : String := "c7a474d93f38f11a5cc3e263e9799eee8c7880217f938ce567c987f458b266ff"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 589 := ![
  2,
  3,
  6,
  9,
  10,
  11,
  16,
  25,
  32,
  37,
  235,
  242,
  254,
  263,
  292,
  322,
  360,
  362,
  372,
  373,
  377,
  379,
  383,
  384,
  397,
  430,
  472,
  548,
  584,
  585,
  586,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (5, 1), (17, 1), (25, 1), (32, 1), (38, 1), (50, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (7, 1), (17, 1), (31, 1), (32, 1), (38, 1), (50, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (17, 1), (32, 1), (33, 1), (50, 1), (55, 1), (58, 2)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (17, 1), (31, 1), (38, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (28, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (25, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (25, 1), (38, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (23, 1), (31, 1), (38, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (4, 1), (22, 1), (25, 1), (38, 1), (44, 1), (50, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 2), (7, 1), (22, 1), (31, 1), (38, 1), (44, 1), (50, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 2), (22, 1), (33, 1), (44, 1), (50, 1), (55, 1), (58, 2)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (8, 1), (22, 1), (25, 1), (29, 1), (38, 1), (44, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (31, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (8, 1), (22, 1), (29, 1), (31, 1), (38, 1), (44, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (22, 1), (29, 1), (33, 1), (44, 1), (55, 1), (58, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (7, 1), (26, 1), (31, 1), (38, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (25, 1), (29, 1), (38, 1), (53, 2)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (26, 1), (31, 1), (33, 1), (38, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (29, 1), (33, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (31, 1), (38, 1), (53, 2), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (31, 1), (38, 1), (44, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (25, 1), (32, 1), (38, 2), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (21, 1), (31, 1), (33, 1), (38, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (32, 1), (33, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (23, 1), (31, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (31, 1), (34, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (4, 1), (38, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(2, 2), (14, 1), (38, 1), (53, 2), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (31, 1), (35, 1), (38, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (7, 1), (31, 1), (38, 1), (53, 1), (56, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (34, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (31, 1), (34, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (4, 1), (25, 1), (38, 1), (48, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 2), (7, 1), (31, 1), (38, 1), (48, 1), (50, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 2), (33, 1), (48, 1), (50, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (8, 1), (25, 1), (29, 1), (38, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (8, 1), (29, 1), (31, 1), (38, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (29, 1), (33, 1), (48, 1), (55, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (5, 1), (25, 1), (32, 1), (38, 1), (42, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (7, 1), (31, 1), (32, 1), (38, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (32, 1), (33, 1), (42, 1), (55, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (16, 1), (25, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (16, 1), (31, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (33, 1), (55, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (12, 1), (25, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (12, 1), (31, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (33, 1), (55, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (5, 1), (25, 1), (32, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (7, 1), (31, 1), (32, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (32, 1), (33, 1), (55, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (4, 1), (25, 1), (38, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 2), (7, 1), (31, 1), (38, 1), (50, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 2), (33, 1), (50, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (8, 1), (25, 1), (29, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (8, 1), (29, 1), (31, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (29, 1), (33, 1), (55, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (38, 1), (53, 2), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (25, 1), (38, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (33, 1), (38, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (8, 1), (31, 1), (38, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (38, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (25, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (55, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (31, 1), (37, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (38, 2), (52, 1), (53, 2), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (42, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (4, 1), (22, 1), (25, 1), (38, 1), (44, 1), (48, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 2), (7, 1), (22, 1), (31, 1), (38, 1), (44, 1), (48, 1), (50, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 2), (22, 1), (33, 1), (44, 1), (48, 1), (50, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (5, 1), (17, 1), (25, 1), (32, 1), (38, 1), (42, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (8, 1), (22, 1), (25, 1), (29, 1), (38, 1), (44, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (31, 1), (38, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (7, 1), (17, 1), (31, 1), (32, 1), (38, 1), (42, 1), (50, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (17, 1), (32, 1), (33, 1), (42, 1), (50, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (8, 1), (22, 1), (29, 1), (31, 1), (38, 1), (44, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (17, 1), (31, 1), (38, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (23, 1), (31, 1), (38, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (28, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (22, 1), (29, 1), (33, 1), (44, 1), (48, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (25, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (25, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component56.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component56.SelectedLeafB5
