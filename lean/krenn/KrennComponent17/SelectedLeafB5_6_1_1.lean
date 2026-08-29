import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_1_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b64541a04fc32ee903f4bc87fa5ea7df17d7384f97148248e0d55d8badd841b9"
def certificateSHA256 : String := "c719d0a943bcb5ca713a40ff4dea73030fe69f404b2bd366528cdef261049ba6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 614 := ![
  30,
  206,
  300,
  306,
  308,
  309,
  330,
  410,
  454,
  490,
  523,
  535,
  555,
  570,
  578,
  594,
  600,
  603,
  604,
  605,
  609,
  610,
  611,
  612
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (43, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (43, 1), (49, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (49, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (49, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (49, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (49, 1), (50, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (49, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (49, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(49, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (40, 1), (61, 2)] }],
  [{ coefficient := -1, powers := [(9, 1), (15, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (37, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (49, 1), (61, 2)] }, { coefficient := 1, powers := [(9, 1), (44, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (34, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (28, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (19, 1), (22, 1), (49, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (39, 1), (40, 1), (61, 2)] }, { coefficient := -1, powers := [(1, 1), (9, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (21, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (21, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (49, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (49, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (21, 1), (50, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (34, 1), (37, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (21, 1), (44, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (34, 1), (37, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (21, 1), (40, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (34, 1), (37, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (49, 1), (50, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(43, 1), (49, 1), (51, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (9, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (40, 1), (61, 2)] }, { coefficient := 1, powers := [(9, 1), (11, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (39, 1), (40, 1), (61, 2)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (44, 1), (61, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_1_1.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_1_1
