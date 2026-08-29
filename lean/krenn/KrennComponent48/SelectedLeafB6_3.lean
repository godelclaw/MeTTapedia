import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component48.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4210ac1d21999769bd5b369785f52ed803710d7102adb749d9e18890ad06358a"
def certificateSHA256 : String := "657a91c9354e3189a2f744be895015addc12862ec5ace6b6171dd71e79cee655"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 641 := ![
  2,
  4,
  5,
  14,
  26,
  30,
  59,
  162,
  166,
  168,
  182,
  206,
  228,
  229,
  239,
  259,
  345,
  348,
  356,
  359,
  360,
  364,
  429,
  438,
  443,
  558,
  562,
  576,
  577,
  627,
  632,
  634,
  635,
  636,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (14, 1), (22, 2), (33, 1), (56, 1), (61, 2)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (22, 1), (33, 1), (43, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (22, 1), (32, 1), (33, 1), (37, 1), (56, 1), (61, 2)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (22, 1), (33, 1), (43, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (22, 1), (33, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (33, 1), (34, 1), (37, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (10, 1), (32, 1), (33, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (14, 1), (32, 1), (33, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (27, 1), (31, 1), (33, 1), (37, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (43, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (48, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1), (50, 2), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (53, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (31, 1), (33, 1), (37, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (31, 1), (33, 1), (37, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (33, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (31, 1), (33, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (14, 1), (22, 1), (33, 1), (56, 1), (61, 2)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (32, 1), (33, 1), (37, 1), (56, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (43, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (30, 1), (42, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (32, 1), (33, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (33, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (33, 1), (37, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (43, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (14, 1), (22, 1), (33, 1), (49, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (32, 1), (33, 1), (37, 1), (49, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (43, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(42, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (33, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (10, 1), (32, 1), (33, 1), (37, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (14, 1), (15, 1), (22, 1), (27, 1), (33, 1), (56, 1), (61, 2)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (14, 1), (27, 1), (33, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (14, 1), (32, 1), (33, 1), (37, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (15, 1), (27, 1), (33, 1), (43, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (25, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (15, 1), (20, 1), (27, 1), (32, 1), (33, 1), (37, 1), (56, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (25, 1), (32, 1), (33, 1), (37, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (20, 1), (27, 1), (33, 1), (43, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (20, 1), (27, 1), (33, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (33, 1), (34, 1), (37, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (31, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (30, 1), (42, 1), (50, 2), (62, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component48.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component48.SelectedLeafB6_3
