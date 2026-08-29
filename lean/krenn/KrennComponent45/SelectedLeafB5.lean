import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component45.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "160ba482c846f1109b0857ea7962554037b4e5aebe72e85a5f5aae19df426cf1"
def certificateSHA256 : String := "41849e89cd4fedd27025af867855d3e02bd10794658e34f8c57b51b3c2200aef"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 563 := ![
  0,
  1,
  2,
  4,
  17,
  20,
  34,
  48,
  203,
  208,
  214,
  231,
  237,
  241,
  244,
  245,
  255,
  258,
  267,
  284,
  360,
  362,
  365,
  367,
  372,
  379,
  380,
  381,
  384,
  390,
  407,
  421,
  422,
  468,
  492,
  525,
  557,
  559,
  560,
  562
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 59) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (40, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (31, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (36, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (25, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (40, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (40, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (34, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (25, 1), (39, 1), (55, 1), (57, 2)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (39, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (30, 1), (34, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (39, 1), (55, 1), (57, 2)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (52, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (36, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (14, 1), (33, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (18, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (40, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (46, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (33, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (50, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (39, 1), (56, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (39, 1), (55, 1), (57, 2)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (57, 2)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (34, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (40, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (39, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (46, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (46, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (39, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (39, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (46, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (40, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (40, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (39, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (34, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (31, 1), (33, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (36, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (25, 1), (33, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (40, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (40, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }]
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

#print axioms Krenn.Component45.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component45.SelectedLeafB5
