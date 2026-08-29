import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fff11a5b3b38aa0bfd0717706633165cf0b13e50f167f610698361a24f6459c1"
def certificateSHA256 : String := "91c941e28c5aa1386ffcbce6f54b48ae7d301f610da3487ded7ab8f6ddadb742"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 670 := ![
  2,
  15,
  23,
  166,
  323,
  330,
  442,
  461,
  471,
  480,
  486,
  504,
  584,
  585,
  612,
  614,
  663,
  664,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (38, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (38, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (49, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (34, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (34, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (37, 1), (43, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (37, 1), (38, 1), (53, 2)] }, { coefficient := -2, powers := [(0, 1), (21, 1), (37, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (37, 1), (38, 1), (57, 2)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (38, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (38, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (21, 1), (37, 1), (53, 2)] }, { coefficient := -2, powers := [(6, 1), (20, 1), (21, 1), (37, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (21, 1), (37, 1), (57, 2)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (37, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (37, 1), (48, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (38, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (38, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (38, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (38, 1), (51, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (51, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (34, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (34, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (53, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 2), (63, 1)] }, { coefficient := 2, powers := [(20, 1), (21, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (57, 2), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1), (53, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (53, 2), (63, 1)] }, { coefficient := 2, powers := [(20, 1), (51, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 2), (63, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (37, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (26, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (53, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (53, 2), (63, 1)] }, { coefficient := -2, powers := [(20, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (57, 2), (63, 1)] }, { coefficient := -1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [(62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (51, 1), (53, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (51, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (51, 1), (53, 2), (63, 1)] }, { coefficient := -2, powers := [(20, 1), (21, 1), (51, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (51, 1), (57, 2), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(53, 1)] }, { coefficient := -1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (26, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (48, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (43, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (43, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (49, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (49, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (49, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (49, 1), (55, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (34, 1), (38, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (34, 1), (38, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (34, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (20, 1), (34, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (20, 1), (34, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (26, 1), (51, 1), (53, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (26, 1), (51, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (26, 1), (51, 1), (53, 2), (63, 1)] }, { coefficient := 2, powers := [(20, 1), (21, 1), (26, 1), (51, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (26, 1), (51, 1), (57, 2), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (53, 2)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (53, 2)] }, { coefficient := 2, powers := [(20, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (57, 2)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB4_1
