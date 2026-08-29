import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1b100cfd389a573fe2a4708245d608af08e1ec7f694f7cfefebfd31d54b6e571"
def certificateSHA256 : String := "6a9d34e004fe4a70ce94e3aad824af9bc561ec6803b4f4860aef94cf87d33ee9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 673 := ![
  2,
  15,
  23,
  128,
  147,
  153,
  154,
  155,
  160,
  161,
  258,
  259,
  281,
  282,
  299,
  300,
  301,
  307,
  316,
  323,
  324,
  328,
  330,
  333,
  417,
  419,
  452,
  457,
  462,
  471,
  486,
  488,
  531,
  585,
  588,
  598,
  612,
  613,
  663,
  664,
  668,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(3, 1), (25, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (45, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (31, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (31, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(20, 1), (31, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(21, 1), (31, 1), (45, 1), (51, 1), (62, 2)] }, { coefficient := -2, powers := [(21, 1), (31, 1), (45, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(26, 1), (31, 1), (49, 1), (51, 1), (62, 2)] }, { coefficient := -2, powers := [(26, 1), (31, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 3, powers := [(31, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(31, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (31, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (31, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1), (43, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (31, 1), (46, 1), (62, 1)] }, { coefficient := 2, powers := [(31, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (31, 1), (45, 1), (62, 1)] }, { coefficient := -2, powers := [(26, 1), (31, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (31, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(31, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(20, 1), (31, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(31, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (21, 1), (31, 1), (51, 1), (62, 2)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (43, 1), (53, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (48, 1), (51, 1), (53, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 4, powers := [(18, 1), (21, 1), (31, 1), (45, 1), (62, 2)] }, { coefficient := 2, powers := [(18, 1), (26, 1), (31, 1), (49, 1), (62, 2)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (31, 1), (46, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (31, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 2, powers := [(26, 2), (31, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (43, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (21, 1), (31, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (43, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (48, 1), (51, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(20, 1), (31, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(21, 1), (31, 1), (45, 1), (62, 1)] }, { coefficient := 2, powers := [(26, 1), (31, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (31, 1), (62, 1)] }, { coefficient := -2, powers := [(20, 1), (31, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (49, 1), (53, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (49, 1), (51, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (21, 1), (31, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (26, 1), (31, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (20, 1), (31, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (21, 1), (49, 1), (51, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 2), (31, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (21, 1), (31, 1), (45, 1), (62, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (26, 1), (31, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (31, 1), (49, 1)] }, { coefficient := -2, powers := [(14, 1), (26, 2), (31, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (31, 1), (49, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := -2, powers := [(3, 1), (14, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (42, 1), (43, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_3_0.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_3_0
