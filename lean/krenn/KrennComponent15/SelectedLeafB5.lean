import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b5a75ad00ea99974fed75c7c6bd0befaf389cf23d24007783ffbafed130c1b86"
def certificateSHA256 : String := "cf05b6d1df004ee003bafed50cba589e1773769cb9bfad464fe868e4d6c2f1a7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 589 := ![
  7,
  9,
  10,
  13,
  14,
  17,
  20,
  26,
  29,
  33,
  37,
  43,
  44,
  45,
  210,
  224,
  230,
  245,
  336,
  340,
  360,
  362,
  363,
  364,
  365,
  367,
  368,
  381,
  385,
  386,
  420,
  421,
  495,
  545,
  546,
  584,
  585,
  586,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 59) := ![
  [{ coefficient := -1, powers := [(2, 1), (15, 1), (24, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (24, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (19, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (19, 1), (32, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (31, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (31, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (12, 1), (31, 1), (32, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (19, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (19, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (24, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (29, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (29, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (38, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (31, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (34, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (34, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (38, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (38, 1), (40, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (43, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (28, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (15, 1), (31, 1), (38, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (21, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (32, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (32, 1), (35, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (32, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (15, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(12, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (38, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (37, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (37, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (34, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (31, 1), (38, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (24, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (31, 1), (32, 1), (38, 1), (48, 1)] }, { coefficient := -2, powers := [(4, 1), (12, 1), (31, 1), (32, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (19, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (24, 1), (29, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (19, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (24, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (19, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (29, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (12, 1), (19, 1), (32, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (35, 1), (42, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (29, 1), (35, 1), (48, 1)] }]
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
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB5
